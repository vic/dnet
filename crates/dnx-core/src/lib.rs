#![forbid(unsafe_code)]

mod arena;
mod blob;
mod canonical_hash;
mod class;
pub mod effect;
mod error;
pub mod funeq;
mod lopath;
mod net;
mod port;
pub mod prim;
mod reduce;
mod slot;

pub use blob::{from_blob, to_blob};
pub use canonical_hash::{canonical_hash, ArtifactLocal, Blake3Hash, Interner};
pub use class::{
    Canonical, IsEraNet, IsRepNet, NetClassMarker, NetState, Proper, ΔA, ΔI, ΔK, ΔL
};
pub use error::{DnxError, LinError};
pub use funeq::fn_eq;
pub use lopath::LOPath;
pub use net::{AgentPorts, Net, SlotView};
pub(crate) use port::PrincipalPortId;
pub use port::{PortId, PortKind};
pub use reduce::gpu::{normalize_gpu_batched, GpuOutput};
pub use reduce::parallel::normalize_parallel;
pub use reduce::whnf::{force_whnf, force_whnf_with_prims, NormalizeConfig, ValueHead};
pub use reduce::{
    finalize_canonical, normalize, normalize_demand, normalize_with_prims, CRules, ReduceStats,
};
