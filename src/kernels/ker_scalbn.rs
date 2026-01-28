//! The kernels for scalbn for 32 and 64 bit floating-point numbers.

use crate::helpers::construct::{f32_construct, f64_construct};
use crate::helpers::extract::{
    f32_get_exp_from_bits, f32_get_frac_from_bits, f32_get_sign_from_bits, f64_get_exp_from_bits,
    f64_get_frac_from_bits, f64_get_sign_from_bits,
};
#[must_use]
#[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
pub const fn scalbn_impl_from_bits(bits: u64, n: i32) -> u64 {
    let sign = f64_get_sign_from_bits(bits);
    let frac = f64_get_frac_from_bits(bits);
    let mut exp = f64_get_exp_from_bits(bits) as i32;
    exp += n;
    f64_construct(sign, exp as u64, frac)
}
#[must_use]
#[allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]
#[inline]
pub const fn scalbnf_impl_from_bits(bits: u32, n: i32) -> u32 {
    let sign = f32_get_sign_from_bits(bits);
    let frac = f32_get_frac_from_bits(bits);
    let mut exp = f32_get_exp_from_bits(bits) as i32;
    exp += n;
    f32_construct(sign, exp as u32, frac)
}

pub const fn scalbn_impl(f: f64, n: i32) -> f64 {
    f64::from_bits(scalbn_impl_from_bits(f.to_bits(), n))
}

pub const fn scalbnf_impl(f: f32, n: i32) -> f32 {
    f32::from_bits(scalbnf_impl_from_bits(f.to_bits(), n))
}
