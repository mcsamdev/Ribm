use super::consts::{
    DBL_EXP_BIAS, DBL_EXP_MASK, DBL_EXP_SHIFT, DBL_SIGN_MASK, DBL_SIGN_SHIFT, FLT_EXP_BIAS,
    FLT_EXP_MASK, FLT_EXP_SHIFT, FLT_FRAC_MASK, FLT_FRAC_SHIFT, FLT_SIGN_MASK, FLT_SIGN_SHIFT,
};

/// Extracts the sign bit from the raw bit representation of a 32-bit floating-point number.
///
/// # Arguments
///
/// * `bits` - A `u32` representing the raw bit pattern of an `f32`.
///
/// # Returns
///
/// Returns the sign bit as a `u32` (shifted to the least significant bit position).
/// * `0` indicates a positive number.
/// * `1` indicates a negative number.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_sign_from_bits;
///
/// assert_eq!(f32_get_sign_from_bits(0x3F80_0000), 0); // 1.0 is positive
/// assert_eq!(f32_get_sign_from_bits(0xBF80_0000), 1); // -1.0 is negative
/// ```
#[must_use]
#[inline]
pub const fn f32_get_sign_from_bits(bits: u32) -> u32 {
    (bits & FLT_SIGN_MASK) >> FLT_SIGN_SHIFT
}

/// Extracts the sign bit directly from a 32-bit floating-point number.
///
/// # Arguments
///
/// * `f` - The `f32` value to extract the sign from.
///
/// # Returns
///
/// Returns `0` if `f` is positive, and `1` if `f` is negative.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_sign;
///
/// assert_eq!(f32_get_sign(1.0), 0);
/// assert_eq!(f32_get_sign(-1.0), 1);
/// ```
#[must_use]
#[inline]
pub const fn f32_get_sign(f: f32) -> u32 {
    f32_get_sign_from_bits(f.to_bits())
}

/// Extracts the biased exponent from the raw bit representation of a 32-bit floating-point number.
///
/// # Arguments
///
/// * `bits` - A `u32` representing the raw bit pattern of an `f32`.
///
/// # Returns
///
/// Returns the biased exponent as a `u32`. For standard IEEE 754 `f32`, the bias is 127.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_exp_from_bits;
///
/// // 1.0 (0x3F80_0000) has an exponent of 127 (0x7F)
/// assert_eq!(f32_get_exp_from_bits(0x3F80_0000), 127);
/// ```
#[must_use]
#[inline]
pub const fn f32_get_exp_from_bits(bits: u32) -> u32 {
    (bits & FLT_EXP_MASK) >> FLT_EXP_SHIFT
}

/// Extracts the biased exponent directly from a 32-bit floating-point number.
///
/// # Arguments
///
/// * `f` - The `f32` value to extract the exponent from.
///
/// # Returns
///
/// Returns the biased exponent of `f`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_exp;
///
/// assert_eq!(f32_get_exp(1.0), 127);
/// assert_eq!(f32_get_exp(2.0), 128);
/// assert_eq!(f32_get_exp(0.5), 126);
/// ```
#[must_use]
#[inline]
pub const fn f32_get_exp(f: f32) -> u32 {
    f32_get_exp_from_bits(f.to_bits())
}

/// Extracts the fractional part (mantissa) from the raw bit representation of a 32-bit floating-point number.
///
/// Note: This returns the stored fraction bits. It does *not* include the implicit leading 1
/// (for normalized numbers).
///
/// # Arguments
///
/// * `bits` - A `u32` representing the raw bit pattern of an `f32`.
///
/// # Returns
///
/// Returns the fractional part as a `u32`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_frac_from_bits;
///
/// // 1.0 is 1.0 * 2^0, so fraction bits are all 0
/// assert_eq!(f32_get_frac_from_bits(0x3F80_0000), 0);
///
/// // 1.5 is 1.1(binary) * 2^0, so fraction bits are 0x400000...
/// // In hex (1.5f32): 0x3FC0_0000. 0xC00000 shifted right? No.
/// // The stored fraction is the part after the decimal point.
/// // 1.5 encoded is 0x3FC0_0000.
/// // Exponent: 0x7F (127). Fraction bits: 0x40_0000.
/// assert_eq!(f32_get_frac_from_bits(0x3FC0_0000), 0x40_0000);
/// ```
#[must_use]
#[inline]
pub const fn f32_get_frac_from_bits(bits: u32) -> u32 {
    (bits & FLT_FRAC_MASK) >> FLT_FRAC_SHIFT
}

/// Extracts the fractional part (mantissa) directly from a 32-bit floating-point number.
///
/// # Arguments
///
/// * `f` - The `f32` value to extract the fraction from.
///
/// # Returns
///
/// Returns the fractional part of `f` as a `u32`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_frac;
///
/// assert_eq!(f32_get_frac(1.0), 0);
/// assert_ne!(f32_get_frac(1.5), 0);
/// ```
#[must_use]
#[inline]
pub const fn f32_get_frac(f: f32) -> u32 {
    f32_get_frac_from_bits(f.to_bits())
}

/// Calculates the unbiased exponent from the raw bits of a 32-bit floating-point number.
///
/// The unbiased exponent is calculated by subtracting the bias ([`FLT_EXP_BIAS`]) from the
/// stored biased exponent. This function uses wrapping subtraction to safely handle
/// potential underflows (e.g., for 0 or subnormal numbers) and casts the result to `i32`.
///
/// # Arguments
///
/// * `bits` - A `u32` representing the raw bit pattern of an `f32`.
///
/// # Returns
///
/// Returns the unbiased exponent as an `i32`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_unbiased_exp_from_bits;
///
/// // 1.0 has biased exp 127. 127 - 127 = 0.
/// assert_eq!(f32_get_unbiased_exp_from_bits(0x3F80_0000), 0);
///
/// // 2.0 has biased exp 128. 128 - 127 = 1.
/// assert_eq!(f32_get_unbiased_exp_from_bits(0x4000_0000), 1);
/// ```
#[must_use]
#[allow(clippy::cast_possible_wrap)]
#[inline]
pub const fn f32_get_unbiased_exp_from_bits(bits: u32) -> i32 {
    f32_get_exp_from_bits(bits).wrapping_sub(FLT_EXP_BIAS) as i32
}

/// Calculates the unbiased exponent directly from a 32-bit floating-point number.
///
/// # Arguments
///
/// * `f` - The `f32` value to extract the unbiased exponent from.
///
/// # Returns
///
/// Returns the unbiased exponent of `f` as an `i32`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f32_get_unbiased_exp;
///
/// assert_eq!(f32_get_unbiased_exp(1.0), 0);
/// assert_eq!(f32_get_unbiased_exp(0.5), -1);
/// ```
#[must_use]
#[inline]
pub const fn f32_get_unbiased_exp(f: f32) -> i32 {
    f32_get_unbiased_exp_from_bits(f.to_bits())
}

/// Extracts the sign bit from the raw bit representation of a 64-bit floating-point number.
///
/// # Arguments
///
/// * `bits` - A `u64` representing the raw bit pattern of an `f64`.
///
/// # Returns
///
/// Returns the sign bit as a `u64`.
/// * `0` indicates a positive number.
/// * `1` indicates a negative number.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f64_get_sign_from_bits;
///
/// assert_eq!(f64_get_sign_from_bits(0x3FF0_0000_0000_0000), 0); // 1.0 is positive
/// assert_eq!(f64_get_sign_from_bits(0xBFF0_0000_0000_0000), 1); // -1.0 is negative
/// ```
#[must_use]
#[inline]
pub const fn f64_get_sign_from_bits(bits: u64) -> u64 {
    (bits & DBL_SIGN_MASK) >> DBL_SIGN_SHIFT
}

/// Extracts the sign bit directly from a 64-bit floating-point number.
///
/// # Arguments
///
/// * `f` - The `f64` value to extract the sign from.
///
/// # Returns
///
/// Returns `0` if `f` is positive, and `1` if `f` is negative.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f64_get_sign;
///
/// assert_eq!(f64_get_sign(1.0), 0);
/// assert_eq!(f64_get_sign(-1.0), 1);
/// ```
#[must_use]
#[inline]
pub const fn f64_get_sign(f: f64) -> u64 {
    f64_get_sign_from_bits(f.to_bits())
}

/// Extracts the biased exponent from the raw bit representation of a 64-bit floating-point number.
///
/// # Arguments
///
/// * `bits` - A `u64` representing the raw bit pattern of an `f64`.
///
/// # Returns
///
/// Returns the biased exponent as a `u64`. For `f64`, the bias is 1023.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f64_get_exp_from_bits;
///
/// // 1.0 (0x3FF0_0000_0000_0000) has an exponent of 1023
/// assert_eq!(f64_get_exp_from_bits(0x3FF0_0000_0000_0000), 1023);
/// ```
#[must_use]
#[inline]
pub const fn f64_get_exp_from_bits(bits: u64) -> u64 {
    (bits & DBL_EXP_MASK) >> DBL_EXP_SHIFT
}

/// Extracts the biased exponent directly from a 64-bit floating-point number.
///
/// # Arguments
///
/// * `f` - The `f64` value to extract the exponent from.
///
/// # Returns
///
/// Returns the biased exponent of `f`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f64_get_exp;
///
/// assert_eq!(f64_get_exp(1.0), 1023);
/// assert_eq!(f64_get_exp(2.0), 1024);
/// ```
#[must_use]
#[inline]
pub const fn f64_get_exp(f: f64) -> u64 {
    f64_get_exp_from_bits(f.to_bits())
}

/// Calculates the unbiased exponent from the raw bits of a 64-bit floating-point number.
///
/// The unbiased exponent is calculated by subtracting the bias ([`DBL_EXP_BIAS`]) from the
/// stored biased exponent. This function uses wrapping subtraction to safely handle
/// cases where the subtraction might underflow (e.g., for 0.0) and casts the result to `i64`.
///
/// # Arguments
///
/// * `bits` - A `u64` representing the raw bit pattern of an `f64`.
///
/// # Returns
///
/// Returns the unbiased exponent as an `i64`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f64_get_unbiased_exp_from_bits;
///
/// // 1.0 has biased exp 1023. 1023 - 1023 = 0.
/// assert_eq!(f64_get_unbiased_exp_from_bits(0x3FF0_0000_0000_0000), 0);
///
/// // 2.0 has biased exp 1024. 1024 - 1023 = 1.
/// assert_eq!(f64_get_unbiased_exp_from_bits(0x4000_0000_0000_0000), 1);
/// ```
#[must_use]
#[allow(clippy::cast_possible_wrap)]
#[inline]
pub const fn f64_get_unbiased_exp_from_bits(bits: u64) -> i64 {
    f64_get_exp_from_bits(bits).wrapping_sub(DBL_EXP_BIAS) as i64
}

/// Calculates the unbiased exponent directly from a 64-bit floating-point number.
///
/// # Arguments
///
/// * `f` - The `f64` value to extract the unbiased exponent from.
///
/// # Returns
///
/// Returns the unbiased exponent of `f` as an `i64`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::extract::f64_get_unbiased_exp;
///
/// assert_eq!(f64_get_unbiased_exp(1.0), 0);
/// assert_eq!(f64_get_unbiased_exp(0.5), -1);
/// ```
#[must_use]
#[inline]
pub const fn f64_get_unbiased_exp(f: f64) -> i64 {
    f64_get_unbiased_exp_from_bits(f.to_bits())
}
