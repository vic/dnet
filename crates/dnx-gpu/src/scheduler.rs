/// GpuScheduler — wgpu compute R1-R7 parallel reduction.
/// Implements dnx_sched::Scheduler. Falls back to SequentialScheduler if no GPU adapter found.
/// C2/C3/C4/C1: always on CPU coordinator.
use dnx_core::{
    normalize_gpu_batched, CRules, Canonical, DnxError, GpuOutput, LOPath, Net, PortId, Proper,
    ReduceStats,
};
use dnx_sched::{sequential::SequentialScheduler, Scheduler};
use std::sync::{Mutex, OnceLock};

const WGSL: &str = include_str!("rewrite.wgsl");
const OUT_STRIDE: u64 = 96 * 4; // bytes per thread in out_buf
const MAX_BATCH: u64 = 65536; // max pairs per kernel launch
const MAX_ARENA: u64 = 1 << 22; // 4MB arena = 131072 slots × 32B

pub struct GpuScheduler {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    pair_buf: wgpu::Buffer,
    arena_buf: wgpu::Buffer,
    out_buf: wgpu::Buffer,
    params_buf: wgpu::Buffer,
    readback_buf: wgpu::Buffer,
    bind_group: wgpu::BindGroup,
}

impl GpuScheduler {
    /// Try to create a GpuScheduler using the default wgpu adapter.
    /// Returns None if no GPU adapter is available (CI/embedded).
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
            label: Some("rewrite"),
            source: wgpu::ShaderSource::Wgsl(WGSL.into()),
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("rewrite_pipeline"),
            layout: None,
            module: &shader,
            entry_point: "rewrite_main",
            compilation_options: Default::default(),
            cache: None,
        });
        let bg_layout = pipeline.get_bind_group_layout(0);

        let pair_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("pairs"),
            size: MAX_BATCH * 32,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let arena_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("arena"),
            size: MAX_ARENA,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let out_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("out"),
            size: MAX_BATCH * OUT_STRIDE,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let params_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("params"),
            size: 16,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let readback_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("readback"),
            size: MAX_BATCH * OUT_STRIDE,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bg"),
            layout: &bg_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: pair_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: arena_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: out_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: params_buf.as_entire_binding(),
                },
            ],
        });

        Some(GpuScheduler {
            device,
            queue,
            pipeline,
            pair_buf,
            arena_buf,
            out_buf,
            params_buf,
            readback_buf,
            bind_group,
        })
    }

    fn run_batch(
        &self,
        pairs: &[(PortId, PortId, LOPath)],
        arena_words: &[u32],
        bases: &[u32],
    ) -> Result<Vec<GpuOutput>, DnxError> {
        let n = pairs.len() as u32;
        if n == 0 {
            return Ok(Vec::new());
        }

        let pair_bytes = encode_pairs(pairs);
        let arena_bytes = words_to_bytes(arena_words);
        let out_bytes_len = n as u64 * OUT_STRIDE;

        // Upload inputs into pre-allocated buffers — no allocation per batch.
        self.queue.write_buffer(&self.pair_buf, 0, &pair_bytes);
        self.queue.write_buffer(&self.arena_buf, 0, &arena_bytes);
        self.queue
            .write_buffer(&self.params_buf, 0, &words_to_bytes(&[bases[0], n, 0, 0]));

        let mut encoder = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = encoder.begin_compute_pass(&Default::default());
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &self.bind_group, &[]);
            pass.dispatch_workgroups(n.div_ceil(128), 1, 1);
        }
        encoder.copy_buffer_to_buffer(&self.out_buf, 0, &self.readback_buf, 0, out_bytes_len);
        self.queue.submit([encoder.finish()]);

        let slice = self.readback_buf.slice(..out_bytes_len);
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

        let outputs = (0..n as usize)
            .map(|i| parse_output(&words, i, bases[i]))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(outputs)
    }
}

static GLOBAL_GPU: OnceLock<Option<Mutex<GpuScheduler>>> = OnceLock::new();

fn global_gpu() -> Option<&'static Mutex<GpuScheduler>> {
    GLOBAL_GPU
        .get_or_init(|| GpuScheduler::try_new().map(Mutex::new))
        .as_ref()
}

impl Scheduler for GpuScheduler {
    fn normalize<C: CRules>(
        net: Net<Proper, C>,
    ) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
        match global_gpu() {
            Some(mu) => {
                let gpu = mu.lock().map_err(|_| DnxError::ArenaCapacityExceeded)?;
                normalize_gpu_batched(net, |pairs, arena_words, bases| {
                    gpu.run_batch(pairs, arena_words, bases)
                })
            }
            None => SequentialScheduler::normalize(net),
        }
    }
}

// ---- encoding helpers ----

fn encode_pairs(pairs: &[(PortId, PortId, LOPath)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(pairs.len() * 32);
    for (p0, p1, lo) in pairs {
        let (bits, len) = lo.gpu_bits();
        let words: [u32; 8] = [
            p0.raw(),
            p1.raw(),
            bits[0],
            bits[1],
            bits[2],
            bits[3],
            len as u32,
            0,
        ];
        for w in words {
            out.extend_from_slice(&w.to_le_bytes());
        }
    }
    out
}

fn words_to_bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn parse_output(words: &[u32], i: usize, _base: u32) -> Result<GpuOutput, DnxError> {
    let ob = i * 96;

    let na_count = words[ob] as usize;
    let mut new_agents = Vec::with_capacity(na_count);
    for k in 0..na_count {
        let tag = words[ob + 1 + k] as u8;
        let data = words[ob + 5 + k] as u16;
        let d0 = (words[ob + 9 + k] as u16) as i16;
        let d1 = (words[ob + 13 + k] as u16) as i16;
        if data == 0xFFFF {
            return Err(DnxError::DeltaOverflow);
        }
        new_agents.push((tag, data, d0, d1));
    }

    let ret_count = words[ob + 17] as usize;
    let retired: Vec<u32> = words[ob + 18..ob + 18 + ret_count].to_vec();

    let conn_count = words[ob + 20] as usize;
    let mut connects = Vec::with_capacity(conn_count);
    for j in 0..conn_count {
        let co = ob + 21 + j * 8;
        let a = PortId::from_raw(words[co]);
        let b = PortId::from_raw(words[co + 1]);
        let lo = LOPath::from_gpu_bits(
            words[co + 2],
            words[co + 3],
            words[co + 4],
            words[co + 5],
            words[co + 6] as u8,
        );
        connects.push((a, b, lo));
    }

    let er_count = words[ob + 85] as usize;
    let set_erasers: Vec<PortId> = words[ob + 86..ob + 86 + er_count]
        .iter()
        .map(|&r| PortId::from_raw(r))
        .collect();

    let has_link = words[ob + 90] != 0;
    let link_direct = if has_link {
        Some((
            PortId::from_raw(words[ob + 91]),
            PortId::from_raw(words[ob + 92]),
        ))
    } else {
        None
    };

    Ok(GpuOutput {
        new_agents,
        retired,
        connects,
        set_erasers,
        link_direct,
    })
}
