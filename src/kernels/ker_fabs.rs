//! The kernel for 32 and 64 bit floating point absolute value function.

use crate::helpers::consts::{DBL_SIGN_MASK, FLT_SIGN_MASK};
pub const fn fabs_impl_from_bits(bits: u64) -> u64 {
    bits & !DBL_SIGN_MASK
}

pub const fn fabsf_impl_from_bits(bits: u32) -> u32 {
    bits & !FLT_SIGN_MASK
}

pub const fn fabs_impl(f: f64) -> f64 {
    let bits = f.to_bits();
    f64::from_bits(fabs_impl_from_bits(bits))
}

pub const fn fabsf_impl(f: f32) -> f32 {
    let bits = f.to_bits();
    f32::from_bits(fabsf_impl_from_bits(bits))
}
