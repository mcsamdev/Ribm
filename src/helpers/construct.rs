use super::consts::{
    DBL_EXP_ALL_ONES, DBL_EXP_SHIFT, DBL_FRAC_MASK, DBL_SIGN_NEG, DBL_SIGN_SHIFT, FLT_EXP_ALL_ONES,
    FLT_EXP_SHIFT, FLT_FRAC_MASK, FLT_SIGN_NEG, FLT_SIGN_SHIFT,
};

/// Constructs a 32-bit floating-point number from its unpacked sign, exponent, and fraction parts.
///
/// This function packs the three components of an IEEE 754 single-precision float into
/// a raw `u32`. It handles bitwise positioning and masking to ensure that extra bits
/// in the inputs do not corrupt adjacent fields.
///
/// # Arguments
///
/// * `sign` - The sign bit. Only the least significant bit is used:
///   * `0` for positive.
///   * `1` for negative.
/// * `exp` - The biased exponent. Only the lower 8 bits are used.
///   * Range: `0` to `255`.
///   * Bias: `127`.
/// * `frac` - The fractional part (mantissa) without the implicit leading 1. Only the lower 23 bits are used.
///
/// # Returns
///
/// Returns the packed `u32` bit pattern representing the floating-point number.
///
/// # Examples
///
/// ```rust
/// use ribm::helpers::construct::f32_construct;
///
/// // Construct 1.0: Sign=0, Biased Exp=127 (0x7F), Frac=0
/// let one_bits = f32_construct(0, 127, 0);
/// assert_eq!(f32::from_bits(one_bits), 1.0);
///
/// // Construct -1.0: Sign=1, Biased Exp=127, Frac=0
/// let neg_one_bits = f32_construct(1, 127, 0);
/// assert_eq!(f32::from_bits(neg_one_bits), -1.0);
///
/// // Construct Smallest Subnormal: Sign=0, Exp=0, Frac=1
/// let min_subnormal = f32_construct(0, 0, 1);
/// assert_eq!(min_subnormal, 0x0000_0001);
/// ```
#[must_use]
#[inline]
pub const fn f32_construct(sign: u32, exp: u32, frac: u32) -> u32 {
    ((sign & FLT_SIGN_NEG) << FLT_SIGN_SHIFT)
        | ((exp & FLT_EXP_ALL_ONES) << FLT_EXP_SHIFT)
        | (frac & FLT_FRAC_MASK)
}

/// Constructs a 64-bit floating-point number from its unpacked sign, exponent, and fraction parts.
///
/// This function packs the three components of an IEEE 754 double-precision float into
/// a raw `u64`. It handles bitwise positioning and masking to ensure that extra bits
/// in the inputs do not corrupt adjacent fields.
///
/// # Arguments
///
/// * `sign` - The sign bit. Only the least significant bit is used:
///   * `0` for positive.
///   * `1` for negative.
/// * `exp` - The biased exponent. Only the lower 11 bits are used.
///   * Range: `0` to `2047`.
///   * Bias: `1023`.
/// * `frac` - The fractional part (mantissa) without the implicit leading 1. Only the lower 52 bits are used.
///
/// # Returns
///
/// Returns the packed `u64` bit pattern representing the floating-point number.
///
/// # Examples
///
/// ```rust
/// use ribm::helpers::construct::f64_construct;
///
/// // Construct 1.0: Sign=0, Biased Exp=1023 (0x3FF), Frac=0
/// let one_bits = f64_construct(0, 1023, 0);
/// assert_eq!(f64::from_bits(one_bits), 1.0);
///
/// // Construct -2.0: Sign=1, Biased Exp=1024 (0x400), Frac=0
/// let neg_two_bits = f64_construct(1, 1024, 0);
/// assert_eq!(f64::from_bits(neg_two_bits), -2.0);
/// ```
#[must_use]
#[inline]
pub const fn f64_construct(sign: u64, exp: u64, frac: u64) -> u64 {
    ((sign & DBL_SIGN_NEG) << DBL_SIGN_SHIFT)
        | ((exp & DBL_EXP_ALL_ONES) << DBL_EXP_SHIFT)
        | (frac & DBL_FRAC_MASK)
}
