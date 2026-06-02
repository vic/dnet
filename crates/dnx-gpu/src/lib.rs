#![forbid(unsafe_code)]

mod scheduler;
pub use scheduler::GpuScheduler;

mod amortized;
pub use amortized::{encode_net_for_gpu, global_amortized, GpuAmortized};
