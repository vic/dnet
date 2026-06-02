/// Amortized GPU normalizer — GPU writes connections directly to arena.
/// Eliminates CPU coordinator per-round overhead.
/// CPU uploads once (arena + frontier), GPU runs passes, CPU reads back once.
/// R4 (Fan⊗Fan) only. ΔL nets: single round. ΔI nets: multiple rounds.
use dnx_core::{DnxError, Net, Proper, ΔL};
use std::sync::{Mutex, OnceLock};

const WGSL_AM: &str = include_str!("rewrite_am.wgsl");
const MAX_PAIRS: u64 = 1 << 17; // 131072 pairs max per step
const MAX_ARENA: u64 = 1 << 23; // 32MB arena

pub struct GpuAmortized {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    frontier_a: wgpu::Buffer,
    #[allow(dead_code)]
    frontier_b: wgpu::Buffer, // ping-pong target; held for GPU lifetime
    arena_buf: wgpu::Buffer,
    counters_buf: wgpu::Buffer,
    readback_buf: wgpu::Buffer,
    bg_ping: wgpu::BindGroup, // frontier_a → frontier_b
    bg_pong: wgpu::BindGroup, // frontier_b → frontier_a
}

impl GpuAmortized {
    pub fn try_new() -> Option<Self> {
        pollster::block_on(Self::try_new_async())
    }

    async fn try_new_async() -> Option<Self> {
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor::default());
        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions::default())
            .await?;
        let (device, queue) = adapter
            .request_device(&wgpu::DeviceDescriptor::default(), None)
            .await
            .ok()?;

        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("rewrite_am"),
            source: wgpu::ShaderSource::Wgsl(WGSL_AM.into()),
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("am_pipeline"),
            layout: None,
            module: &shader,
            entry_point: "rewrite_am_main",
            compilation_options: Default::default(),
            cache: None,
        });
        let bg_layout = pipeline.get_bind_group_layout(0);

        let pair_bytes = MAX_PAIRS * 32;
        let arena_bytes = MAX_ARENA;

        let frontier_a = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("frontier_a"),
            size: pair_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let frontier_b = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("frontier_b"),
            size: pair_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let arena_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("arena_am"),
            size: arena_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let counters_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("counters"),
            size: 16,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_DST
                | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let readback_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("readback_counters"),
            size: 16,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let bg_ping = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bg_ping"),
            layout: &bg_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: frontier_a.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: arena_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: frontier_b.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: counters_buf.as_entire_binding(),
                },
            ],
        });
        let bg_pong = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bg_pong"),
            layout: &bg_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: frontier_b.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: arena_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: frontier_a.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: counters_buf.as_entire_binding(),
                },
            ],
        });

        Some(GpuAmortized {
            device,
            queue,
            pipeline,
            frontier_a,
            frontier_b,
            arena_buf,
            counters_buf,
            readback_buf,
            bg_ping,
            bg_pong,
        })
    }

    /// Run R4 amortized with pre-encoded arena and pairs.
    /// For benchmark use: caller encodes data in setup (not timed).
    /// Returns interaction count.
    pub fn run_r4_raw(
        &self,
        arena_bytes: &[u8],
        pair_bytes: &[u8],
        n_pairs: u32,
    ) -> Result<u64, DnxError> {
        if n_pairs == 0 {
            return Ok(0);
        }
        self.queue.write_buffer(&self.arena_buf, 0, arena_bytes);
        self.queue.write_buffer(&self.frontier_a, 0, pair_bytes);
        self.queue.write_buffer(
            &self.counters_buf,
            0,
            &words_to_bytes(&[n_pairs, 0u32, 0u32, 0u32]),
        );
        self.run_loop(n_pairs)
    }

    /// Normalize a ΔL net using amortized GPU mode (includes arena encoding).
    pub fn normalize_r4(&self, net: Net<Proper, ΔL>) -> Result<u64, DnxError> {
        let arena_bytes = words_to_bytes(&net.encode_arena_gpu());
        let pairs = net.encode_frontier_gpu();
        if pairs.is_empty() {
            return Ok(0);
        }
        let n_pairs = pairs.len() as u32;
        let pair_bytes = encode_pairs_am(&pairs);
        self.run_r4_raw(&arena_bytes, &pair_bytes, n_pairs)
    }

    fn run_loop(&self, initial_n: u32) -> Result<u64, DnxError> {
        let mut total = 0u64;
        let mut current_n = initial_n;
        let mut ping = true;

        loop {
            if current_n == 0 {
                break;
            }

            let mut encoder = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = encoder.begin_compute_pass(&Default::default());
                pass.set_pipeline(&self.pipeline);
                pass.set_bind_group(0, if ping { &self.bg_ping } else { &self.bg_pong }, &[]);
                pass.dispatch_workgroups(current_n.div_ceil(128), 1, 1);
            }
            encoder.copy_buffer_to_buffer(&self.counters_buf, 0, &self.readback_buf, 0, 16);
            self.queue.submit([encoder.finish()]);
            ping = !ping;

            let slice = self.readback_buf.slice(..);
            let (tx, rx) = std::sync::mpsc::channel();
            slice.map_async(wgpu::MapMode::Read, move |r| {
                let _ = tx.send(r);
            });
            self.device.poll(wgpu::Maintain::Wait);
            rx.recv()
                .map_err(|_| DnxError::ArenaCapacityExceeded)?
                .map_err(|_| DnxError::ArenaCapacityExceeded)?;

            let raw = slice.get_mapped_range();
            let words: Vec<u32> = raw
                .chunks_exact(4)
                .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
                .collect();
            drop(raw);
            self.readback_buf.unmap();

            let new_n = words[1];
            total += words[2] as u64;

            if new_n == 0 {
                break;
            }
            current_n = new_n;
            self.queue.write_buffer(
                &self.counters_buf,
                0,
                &words_to_bytes(&[new_n, 0u32, 0u32, 0u32]),
            );
        }

        Ok(total)
    }
}

static GLOBAL_AM: OnceLock<Option<Mutex<GpuAmortized>>> = OnceLock::new();

pub fn global_amortized() -> Option<&'static Mutex<GpuAmortized>> {
    GLOBAL_AM
        .get_or_init(|| GpuAmortized::try_new().map(Mutex::new))
        .as_ref()
}

pub fn encode_net_for_gpu(net: &Net<Proper, ΔL>) -> (Vec<u8>, Vec<u8>, u32) {
    let arena_bytes = words_to_bytes(&net.encode_arena_gpu());
    let pairs = net.encode_frontier_gpu();
    let n = pairs.len() as u32;
    let pair_bytes = encode_pairs_am(&pairs);
    (arena_bytes, pair_bytes, n)
}

fn encode_pairs_am(pairs: &[(u32, u32, [u32; 4], u8)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(pairs.len() * 32);
    for &(p0, p1, bits, len) in pairs {
        let words: [u32; 8] = [p0, p1, bits[0], bits[1], bits[2], bits[3], len as u32, 0];
        for w in words {
            out.extend_from_slice(&w.to_le_bytes());
        }
    }
    out
}

fn words_to_bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}
