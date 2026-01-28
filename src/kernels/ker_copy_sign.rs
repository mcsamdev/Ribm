//! The kernels for the 32 and 64 bit floating point copysign function.

use crate::helpers::consts::{DBL_SIGN_MASK, FLT_SIGN_MASK};
pub const fn copysignf_impl_from_bits(bits_x: u32, bits_y: u32) -> u32 {
    bits_x & !FLT_SIGN_MASK | (bits_y & FLT_SIGN_MASK)
}

pub const fn copysign_impl_from_bits(bits_x: u64, bits_y: u64) -> u64 {
    bits_x & !DBL_SIGN_MASK | (bits_y & DBL_SIGN_MASK)
}

pub const fn copysignf_impl(x: f32, y: f32) -> f32 {
    let bits_x = x.to_bits();
    let bits_y = y.to_bits();
    f32::from_bits(copysignf_impl_from_bits(bits_x, bits_y))
}

pub const fn copysign_impl(x: f64, y: f64) -> f64 {
    let bits_x = x.to_bits();
    let bits_y = y.to_bits();
    f64::from_bits(copysign_impl_from_bits(bits_x, bits_y))
}
