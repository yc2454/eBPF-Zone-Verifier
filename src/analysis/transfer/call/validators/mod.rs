// src/analysis/transfer/call/validators/mod.rs
//
// Category-based validators for BPF helper function arguments.

pub mod map;
pub mod memory;
pub mod nullable;
pub mod scalar;
pub mod socket;

// Re-export validator functions for convenience
pub use map::{validate_const_map_ptr, validate_ptr_to_map_key, validate_ptr_to_map_value};
pub use memory::{validate_ptr_to_alloc_mem, validate_ptr_to_mem, validate_ptr_to_uninit_mem};
pub use nullable::validate_nullable;
pub use scalar::{validate_const_size, validate_const_size_or_zero};
pub use socket::validate_socket_arg;
