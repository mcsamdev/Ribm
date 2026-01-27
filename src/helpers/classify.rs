/*
 * Classification functions for f32 and f64 using constants defines in consts.rs
 * If a number that you would use in here is not in consts.rs, please add it there and use the constant rather than the number
 */

use super::consts::{
    DBL_ABS_MASK, DBL_EXP_MASK, DBL_NEG_INF, DBL_NEG_ZERO, DBL_POS_INF, DBL_POS_ZERO, DBL_QNAN_BIT,
    DBL_SIGN_MASK, FLT_ABS_MASK, FLT_EXP_MASK, FLT_NEG_INF, FLT_NEG_ZERO, FLT_POS_INF,
    FLT_POS_ZERO, FLT_QNAN_BIT, FLT_SIGN_MASK,
};

/// Checks if the given 32-bit representation of a floating-point number (`f32`) corresponds
/// to a "Not a Number" (NaN) value.
///
/// This function operates directly on the bit-level representation of an `f32`. It uses
/// masks to isolate the relevant bits that determine whether the value is NaN:
/// - [`FLT_ABS_MASK`] is used to obtain the absolute value of the floating-point number.
/// - [`FLT_EXP_MASK`] is the bit pattern that represents the maximum exponent for a valid
///   finite floating-point value.
///
/// A value is considered NaN if the absolute value's bit pattern is greater than the exponent
/// bit pattern. Such cases occur because, in IEEE 754 floating-point standard, NaN values
/// have all exponent bits set (an "all-1" exponent field) and at least one bit in the
/// significand (fraction) field set to 1.
///
/// # Arguments
///
/// * `bits` - A `u32` representing the raw bit pattern of an `f32` value.
///
/// # Returns
///
/// Returns `true` if the bit pattern represents a NaN value, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_nan_from_bits;
///
/// let nan_bits: u32 = 0x7FC0_0000; // A common bit representation of NaN
/// assert!(f32_is_nan_from_bits(nan_bits));
///
/// let non_nan_bits: u32 = 0x3F80_0000; // Bit representation of 1.0f32
/// assert!(!f32_is_nan_from_bits(non_nan_bits));
/// ```
///
/// # Note
///
/// This function does not perform any runtime checks; it assumes the input is a valid
/// bit pattern for an `f32`. Supplying arbitrary values may yield unexpected results.
#[must_use]
#[inline]
pub const fn f32_is_nan_from_bits(bits: u32) -> bool {
    (bits & FLT_ABS_MASK) > FLT_EXP_MASK
}

/// Checks whether the given `f32` value is a NaN (Not a Number).
///
/// This function determines if the floating-point value `f` is a NaN by
/// converting it to its raw bit representation and evaluating it accordingly.
///
/// # Arguments
///
/// * `f` - A 32-bit floating-point number (`f32`) to be checked.
///
/// # Returns
///
/// Returns `true` if `f` is a NaN (Not a Number), `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_nan;
///
/// assert!(f32_is_nan(f32::NAN)); // NaN value returns true
/// assert!(!f32_is_nan(1.0));     // Non-NaN value returns false
/// assert!(!f32_is_nan(f32::INFINITY)); // Infinity is not considered NaN
/// ```
///
/// # Note
///
/// This function relies on the [`f32::to_bits`] method to access the underlying
/// bit representation of the floating-point number.
///
/// # See Also
///
/// - [`f32::is_nan`]: A standard library method to check for NaN in `f32` values.
/// - [`f32_is_nan_from_bits`]: The underlying function used for the bit-level check.
#[must_use]
#[inline]
pub const fn f32_is_nan(f: f32) -> bool {
    f32_is_nan_from_bits(f.to_bits())
}

/// Determines if a 32-bit floating-point number, represented by its raw bits, is a quiet NaN (qNaN).
///
/// A quiet NaN (qNaN) is a special form of a NaN (Not-a-Number) value in
/// floating-point representation. qNaNs are used to propagate errors silently
/// through computations without triggering exceptions.
///
/// # Arguments
///
/// * `bits` - A `u32` value representing the raw bits of a 32-bit floating-point number (`f32`).
///
/// # Returns
///
/// Returns `true` if the provided bits represent a quiet NaN (qNaN), `false` otherwise.
///
/// # Details
///
/// The function checks two conditions to determine if the bit pattern corresponds to a qNaN:
/// 1. `(bits & FLT_ABS_MASK) > FLT_EXP_MASK`: Verifies if the absolute value of the
///    floating-point number is greater than the largest possible exponent value for an
///    `f32`, indicating that it's a NaN.
/// 2. `(bits & FLT_QNAN_BIT) != 0`: Ensures that the specific bit representing the
///    "quiet NaN" (qNaN) is set.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_qnan_from_bits;
///
/// const QUIET_NAN_BITS: u32 = 0x7FC0_0000;
/// assert!(f32_is_qnan_from_bits(QUIET_NAN_BITS));
///
/// const SIGNALING_NAN_BITS: u32 = 0x7F80_0001;
/// assert!(!f32_is_qnan_from_bits(SIGNALING_NAN_BITS));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_qnan_from_bits(bits: u32) -> bool {
    (bits & FLT_ABS_MASK) > FLT_EXP_MASK && (bits & FLT_QNAN_BIT) != 0
}

/// Determines whether a given `f32` value is a quiet NaN (qNaN).
///
/// A quiet NaN (qNaN) is a special form of a NaN (Not-a-Number) value in
/// floating-point representation. qNaNs are used to propagate errors silently
/// through computations without triggering exceptions.
///
/// This function uses the bit representation of the input `f32` value to
/// determine if it is a qNaN by delegating the check to the
/// [`f32_is_qnan_from_bits`] function.
///
/// # Arguments
///
/// * `f` - The 32-bit floating-point number (`f32`) to be checked.
///
/// # Returns
///
/// Returns `true` if the input `f` is a quiet NaN, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_qnan;
///
/// let nan_value = f32::from_bits(0x7FC0_0000); // A qNaN example
/// assert!(f32_is_qnan(nan_value));
///
/// let normal_value = 1.0_f32;
/// assert!(!f32_is_qnan(normal_value));
/// ```
///
/// # Note
///
/// This function does not distinguish between signaling NaNs (sNaNs) and
/// non-NaN values; it is specifically designed to detect qNaNs.
#[must_use]
#[inline]
pub const fn f32_is_qnan(f: f32) -> bool {
    f32_is_qnan_from_bits(f.to_bits())
}

/// Determines if a 32-bit floating-point number, represented by its raw bits, is a signaling NaN (sNaN).
///
/// A signaling NaN is a special type of NaN (not-a-number) that differs from a quiet NaN (qNaN)
/// in that its most significant bit in the payload is not set. Signaling NaNs can be used to signal
/// exceptions in floating-point operations.
///
/// # Arguments
///
/// * `bits` - A `u32` representing the raw bit pattern of the 32-bit floating-point number (`f32`).
///
/// # Returns
///
/// Returns `true` if the bit pattern represents a signaling NaN, `false` otherwise.
///
/// # Details
///
/// The function performs the following checks:
/// 1. `(bits & FLT_ABS_MASK) > FLT_EXP_MASK`: This ensures that the value exceeds the exponent
///    mask, identifying it as a NaN.
/// 2. `(bits & FLT_QNAN_BIT) == 0`: This checks that the quiet bit is not set, distinguishing
///    it as a signaling NaN.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_snan_from_bits;
///
/// // Raw bit pattern for signaling NaN
/// let snan_bits: u32 = 0x7FA0_0001;
/// assert!(f32_is_snan_from_bits(snan_bits));
///
/// // Raw bit pattern for quiet NaN
/// let qnan_bits: u32 = 0x7FC0_0000;
/// assert!(!f32_is_snan_from_bits(qnan_bits));
///
/// // Raw bit pattern for a normal floating-point value
/// let normal_bits: u32 = 0x3F80_0000; // 1.0f32
/// assert!(!f32_is_snan_from_bits(normal_bits));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_snan_from_bits(bits: u32) -> bool {
    (bits & FLT_ABS_MASK) > FLT_EXP_MASK && (bits & FLT_QNAN_BIT) == 0
}

/// Determines if the given 32-bit float (`f32`) is a signaling NaN (sNaN).
///
/// A signaling NaN is a special type of NaN (Not-a-Number) that is intended
/// to raise an exception when used in floating-point operations. This function
/// checks if the given `f32` value is an sNaN by analyzing its bit representation.
///
/// # Arguments
///
/// * `f` - The 32-bit floating-point number (`f32`) to check.
///
/// # Returns
///
/// Returns `true` if the provided `f32` represents a signaling NaN, `false` otherwise.
///
/// # Details
///
/// This function internally leverages the [`f32::to_bits`] method to retrieve the
/// bit-level representation of the floating-point number, and delegates the
/// signaling NaN detection logic to the helper function [`f32_is_snan_from_bits`].
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_snan;
///
/// let snan = 0x7F80_0001_u32; // Example bit pattern for a signaling NaN.
/// let snan_value = f32::from_bits(snan);
/// assert!(f32_is_snan(snan_value));
///
/// let normal = 1.0_f32; // A non-NaN value.
/// assert!(!f32_is_snan(normal));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_snan(f: f32) -> bool {
    f32_is_snan_from_bits(f.to_bits())
}

/// Determines whether a 32-bit floating-point number, represented in its raw bitwise format, is infinite.
///
/// # Arguments
///
/// * `bits` - The raw bit representation of a 32-bit floating-point number (`f32`).
///
/// # Returns
///
/// Returns `true` if the input `bits` represents an infinite value (+∞ or -∞), `false` otherwise.
///
/// # Details
///
/// The function uses the IEEE 754 representation of `f32` values to check for infinity.
/// In IEEE 754, infinity is identified when all exponent bits are set (represented by
/// [`FLT_EXP_MASK`]) and the fractional (mantissa) part is 0.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_infinite_from_bits;
///
/// let bits: u32 = 0x7F80_0000; // Positive infinity
/// assert!(f32_is_infinite_from_bits(bits));
///
/// let bits: u32 = 0xFF80_0000; // Negative infinity
/// assert!(f32_is_infinite_from_bits(bits));
///
/// let bits: u32 = 0x7F80_0001; // NaN (not infinity)
/// assert!(!f32_is_infinite_from_bits(bits));
/// ```
///
/// # References
///
/// - [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754)
#[must_use]
#[inline]
pub const fn f32_is_infinite_from_bits(bits: u32) -> bool {
    (bits & FLT_ABS_MASK) == FLT_EXP_MASK
}

/// Checks if a 32-bit floating-point number is infinite (positive or negative infinity).
///
/// This function determines whether the given `f32` value represents an infinite number
/// (either positive infinity or negative infinity) based on its raw bit representation.
///
/// # Arguments
///
/// * `f` - The 32-bit floating-point number to check for infinity.
///
/// # Returns
///
/// Returns `true` if the input is infinite, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_infinite;
///
/// assert!(f32_is_infinite(f32::INFINITY));     // positive infinity
/// assert!(f32_is_infinite(f32::NEG_INFINITY)); // negative infinity
/// assert!(!f32_is_infinite(1.0));              // not infinity
/// assert!(!f32_is_infinite(f32::NAN));         // NaN is not infinity
/// ```
///
/// # Note
///
/// This function relies on [`f32::to_bits`] to retrieve the raw bit representation of the `f32`
/// value and defers the actual infinite check to the [`f32_is_infinite_from_bits`] function.
#[must_use]
#[inline]
pub const fn f32_is_infinite(f: f32) -> bool {
    f32_is_infinite_from_bits(f.to_bits())
}

/// Checks if the provided 32-bit binary representation corresponds
/// to positive infinity in the IEEE 754 floating-point standard.
///
/// # Arguments
///
/// * `bits` - A 32-bit integer representing the raw bits of an `f32` value.
///
/// # Returns
///
/// Returns `true` if the `bits` represent positive infinity ([`FLT_POS_INF`]) in IEEE 754,
/// `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_inf_from_bits;
///
/// const POS_INF_BITS: u32 = 0x7F80_0000; // IEEE 754 representation of positive infinity
/// assert!(f32_is_pos_inf_from_bits(POS_INF_BITS));
///
/// const NOT_POS_INF_BITS: u32 = 0x3F80_0000; // IEEE 754 representation of 1.0
/// assert!(!f32_is_pos_inf_from_bits(NOT_POS_INF_BITS));
/// ```
///
/// # Note
///
/// This function only examines the bit-level representation and does not perform
/// any runtime floating-point operations or conversions.
#[must_use]
#[inline]
pub const fn f32_is_pos_inf_from_bits(bits: u32) -> bool {
    bits == FLT_POS_INF
}

/// Checks if a given 32-bit floating-point number (`f32`) represents positive infinity.
///
/// # Arguments
///
/// * `f` - A 32-bit floating-point number (`f32`) to be checked.
///
/// # Returns
///
/// Returns `true` if the input `f` represents positive infinity (`f32::INFINITY`),
/// `false` otherwise.
///
/// # Details
///
/// Internally, the function converts the `f32` value to its raw memory representation
/// (using [`f32::to_bits`]) and determines if it corresponds to the bit pattern representing
/// positive infinity. Delegates the actual bitwise check to the [`f32_is_pos_inf_from_bits`]
/// helper function.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_inf;
///
/// assert!(f32_is_pos_inf(f32::INFINITY));
/// assert!(!f32_is_pos_inf(42.0));
/// assert!(!f32_is_pos_inf(f32::NEG_INFINITY));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_pos_inf(f: f32) -> bool {
    f32_is_pos_inf_from_bits(f.to_bits())
}

/// Checks whether a 32-bit floating-point number, represented by its raw bits, is negative infinity.
///
/// # Arguments
///
/// * `bits` - A `u32` value representing the raw bit pattern of a 32-bit floating-point number.
///
/// # Returns
///
/// Returns `true` if the given bit pattern corresponds to negative infinity (`-∞`),
/// `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_inf_from_bits;
///
/// const FLT_NEG_INF: u32 = 0xFF80_0000; // Negative infinity in IEEE 754
/// assert!(f32_is_neg_inf_from_bits(FLT_NEG_INF));
/// assert!(!f32_is_neg_inf_from_bits(0x0000_0000)); // Zero is not negative infinity
/// ```
#[must_use]
#[inline]
pub const fn f32_is_neg_inf_from_bits(bits: u32) -> bool {
    bits == FLT_NEG_INF
}

/// Checks if a given 32-bit floating-point number (`f32`) is negative infinity.
///
/// # Arguments
///
/// * `f` - A 32-bit floating-point number (`f32`) to be checked.
///
/// # Returns
///
/// Returns `true` if the input number is negative infinity (`-∞`), `false` otherwise.
///
/// # Details
///
/// This function works by converting the `f32` value into its raw bit representation
/// using the [`f32::to_bits`] method, and then delegating the check to the helper function
/// [`f32_is_neg_inf_from_bits`], which performs the actual negative infinity check.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_inf;
///
/// assert!(f32_is_neg_inf(f32::NEG_INFINITY)); // Returns true
/// assert!(!f32_is_neg_inf(f32::INFINITY));    // Returns false
/// assert!(!f32_is_neg_inf(0.0));              // Returns false
/// assert!(!f32_is_neg_inf(-1.0));             // Returns false
/// ```
#[must_use]
#[inline]
pub const fn f32_is_neg_inf(f: f32) -> bool {
    f32_is_neg_inf_from_bits(f.to_bits())
}

/// Checks if the given bit representation corresponds to the positive zero value (`+0.0f32`)
/// in IEEE 754 floating-point format.
///
/// # Arguments
///
/// * `bits` - The bit representation of an `f32` value.
///
/// # Returns
///
/// Returns `true` if the `bits` represent `+0.0f32` in IEEE 754 format, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_zero_from_bits;
///
/// assert!(f32_is_pos_zero_from_bits(0x0000_0000));  // True - positive zero
/// assert!(!f32_is_pos_zero_from_bits(0x8000_0000)); // False - negative zero
/// assert!(!f32_is_pos_zero_from_bits(0x3F80_0000)); // False - 1.0
/// ```
#[must_use]
#[inline]
pub const fn f32_is_pos_zero_from_bits(bits: u32) -> bool {
    bits == FLT_POS_ZERO
}

/// Checks if a given `f32` floating-point number is positive zero.
///
/// This function determines whether the input `f32` value is exactly positive zero (`+0.0`),
/// without being affected by negative zero (`-0.0`). The function utilizes the bit representation
/// of the number for accurate classification.
///
/// # Arguments
///
/// * `f` - The `f32` floating-point number to be checked.
///
/// # Returns
///
/// Returns `true` if the input is positive zero (`+0.0`), `false` otherwise
/// (e.g., negative zero, nonzero values, or NaN).
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_zero;
///
/// assert!(f32_is_pos_zero(0.0));
/// assert!(!f32_is_pos_zero(-0.0));
/// assert!(!f32_is_pos_zero(1.0));
/// assert!(!f32_is_pos_zero(f32::INFINITY));
/// ```
///
/// # See Also
///
/// This function internally calls [`f32_is_pos_zero_from_bits`], which performs the check
/// based on the bit representation of the floating-point value.
#[must_use]
#[inline]
pub const fn f32_is_pos_zero(f: f32) -> bool {
    f32_is_pos_zero_from_bits(f.to_bits())
}

/// Determines if the given 32-bit floating-point representation (as `u32` bits)
/// corresponds to negative zero (`-0.0`).
///
/// # Arguments
///
/// * `bits` - The 32-bit representation of a floating-point number (in IEEE 754 format).
///
/// # Returns
///
/// Returns `true` if the `bits` represent negative zero (`-0.0`), `false` otherwise.
///
/// # Note
///
/// Negative zero in IEEE 754 has a bit pattern of `0x8000_0000`
/// ([`FLT_NEG_ZERO`] in this context).
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_zero_from_bits;
///
/// const FLT_NEG_ZERO: u32 = 0x8000_0000;
/// assert!(f32_is_neg_zero_from_bits(FLT_NEG_ZERO));
/// assert!(!f32_is_neg_zero_from_bits(0x0000_0000)); // Positive zero
/// assert!(!f32_is_neg_zero_from_bits(0xBF80_0000)); // -1.0
/// ```
#[must_use]
#[inline]
pub const fn f32_is_neg_zero_from_bits(bits: u32) -> bool {
    bits == FLT_NEG_ZERO
}

/// Determines whether the given 32-bit floating-point number (`f32`) is negative zero (`-0.0`).
///
/// # Arguments
///
/// * `f` - The 32-bit floating-point number (`f32`) to check.
///
/// # Returns
///
/// Returns `true` if the provided number is negative zero (`-0.0`), `false` otherwise.
///
/// # Details
///
/// This function relies on the bit representation of the floating-point number.
/// It delegates the actual evaluation to another function, [`f32_is_neg_zero_from_bits`],
/// which performs the bitwise check on the IEEE 754 representation of the input.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_zero;
///
/// assert!(f32_is_neg_zero(-0.0));  // Negative zero
/// assert!(!f32_is_neg_zero(0.0));  // Positive zero
/// assert!(!f32_is_neg_zero(1.0));  // Any non-zero value
/// assert!(!f32_is_neg_zero(-1.0));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_neg_zero(f: f32) -> bool {
    f32_is_neg_zero_from_bits(f.to_bits())
}

/// Checks if the given 32-bit floating-point bit pattern represents a positive quiet NaN (qNaN).
///
/// # Arguments
///
/// * `bits` - A `u32` value representing the raw bit pattern of an IEEE 754 single-precision
///   floating-point number.
///
/// # Returns
///
/// Returns `true` if the bit pattern corresponds to a positive quiet NaN, `false` otherwise.
///
/// # Details
///
/// - A quiet NaN (qNaN) is a special kind of NaN where the most significant bit of the mantissa
///   is set.
/// - This function first checks if the bit pattern represents a qNaN using
///   [`f32_is_qnan_from_bits`].
/// - It then verifies that the sign bit ([`FLT_SIGN_MASK`]) is not set, ensuring that it is
///   positive.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_qnan_from_bits;
///
/// assert!(f32_is_pos_qnan_from_bits(0x7FC0_0000));  // Positive quiet NaN
/// assert!(!f32_is_pos_qnan_from_bits(0xFFC0_0000)); // Negative quiet NaN
/// assert!(!f32_is_pos_qnan_from_bits(0x7F80_0001)); // Positive signaling NaN
/// assert!(!f32_is_pos_qnan_from_bits(0x7F80_0000)); // Positive infinity
/// ```
#[must_use]
#[inline]
pub const fn f32_is_pos_qnan_from_bits(bits: u32) -> bool {
    f32_is_qnan_from_bits(bits) && (bits & FLT_SIGN_MASK) == 0
}

/// Checks if the given 32-bit floating-point number (`f32`) is a positive quiet NaN (qNaN).
///
/// # Arguments
///
/// * `f` - A 32-bit floating-point number (`f32`) to check.
///
/// # Returns
///
/// Returns `true` if the number is a positive quiet NaN, `false` otherwise.
///
/// # Details
///
/// - A NaN is considered "quiet" if the most significant bit of the mantissa is set
///   and the number does not cause exceptions during operations.
/// - This function delegates the check to [`f32_is_pos_qnan_from_bits`], which inspects
///   the underlying representation of the floating-point number using its bit pattern.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_qnan;
///
/// let nan: f32 = f32::NAN;
/// assert!(f32_is_pos_qnan(nan));
///
/// let value: f32 = 1.0;
/// assert!(!f32_is_pos_qnan(value));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_pos_qnan(f: f32) -> bool {
    f32_is_pos_qnan_from_bits(f.to_bits())
}

/// Determines if the given 32-bit representation of a floating-point number
/// corresponds to a negative quiet NaN (qNaN) in the IEEE 754 standard.
///
/// # Arguments
///
/// * `bits` - A `u32` integer representing the raw bit pattern of an `f32`.
///
/// # Returns
///
/// Returns `true` if the bit pattern represents a negative quiet NaN, `false` otherwise.
///
/// # Details
///
/// - A quiet NaN (qNaN) is identified by a specific bit pattern determined
///   by the floating-point format.
/// - A negative quiet NaN is additionally differentiated by having the sign
///   bit set (`1`).
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_qnan_from_bits;
///
/// let positive_qnan_bits: u32 = 0x7FC0_0001; // Quiet NaN with positive sign
/// let negative_qnan_bits: u32 = 0xFFC0_0001; // Quiet NaN with negative sign
///
/// assert!(!f32_is_neg_qnan_from_bits(positive_qnan_bits));
/// assert!(f32_is_neg_qnan_from_bits(negative_qnan_bits));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_neg_qnan_from_bits(bits: u32) -> bool {
    f32_is_qnan_from_bits(bits) && (bits & FLT_SIGN_MASK) != 0
}

/// Checks if a given `f32` value is a negative quiet NaN (qNaN).
///
/// A quiet NaN is a special type of NaN that does not trigger exceptions or
/// signals when used in operations. This function specifically identifies
/// if the provided `f32` value is a negative quiet NaN by interpreting its
/// bit representation.
///
/// # Arguments
///
/// * `f` - A 32-bit floating-point number (`f32`) to be checked.
///
/// # Returns
///
/// Returns `true` if the given `f32` value is a negative quiet NaN, `false` otherwise.
///
/// # Details
///
/// This function internally converts the `f32` value into its bit
/// representation using [`f32::to_bits`] and then determines the result by
/// delegating to the [`f32_is_neg_qnan_from_bits`] function.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_qnan;
///
/// let value = f32::from_bits(0xFFC0_0000); // Negative quiet NaN
/// assert!(f32_is_neg_qnan(value));
///
/// let value = f32::INFINITY;
/// assert!(!f32_is_neg_qnan(value));
///
/// let value = f32::NAN; // Positive quiet NaN
/// assert!(!f32_is_neg_qnan(value));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_neg_qnan(f: f32) -> bool {
    f32_is_neg_qnan_from_bits(f.to_bits())
}

/// Determines if a 32-bit floating-point number (represented by its bit pattern)
/// is a positive signaling NaN (sNaN).
///
/// # Arguments
///
/// * `bits` - A 32-bit unsigned integer representing the raw bit pattern of an `f32` value.
///
/// # Returns
///
/// Returns `true` if the bit pattern represents a positive signaling NaN, `false` otherwise.
///
/// # Details
///
/// This function calls [`f32_is_snan_from_bits`] to check if the bit pattern corresponds
/// to a signaling NaN (sNaN). It then checks that the sign bit (as specified by
/// [`FLT_SIGN_MASK`]) is 0, ensuring the sNaN is positive.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_snan_from_bits;
///
/// assert!(f32_is_pos_snan_from_bits(0x7FA0_0000));  // Positive sNaN
/// assert!(!f32_is_pos_snan_from_bits(0xFFA0_0000)); // Negative sNaN
/// assert!(!f32_is_pos_snan_from_bits(0x7FC0_0000)); // Positive qNaN
/// assert!(!f32_is_pos_snan_from_bits(0x3F80_0000)); // Normal positive number (1.0)
/// ```
#[must_use]
#[inline]
pub const fn f32_is_pos_snan_from_bits(bits: u32) -> bool {
    f32_is_snan_from_bits(bits) && (bits & FLT_SIGN_MASK) == 0
}

/// Checks if a given 32-bit floating-point number (`f32`) is a positive signaling NaN (sNaN).
///
/// A signaling NaN is a special form of NaN that is designed to signal invalid
/// operations. This function specifically checks for positive sNaNs.
///
/// # Arguments
///
/// * `f` - A 32-bit floating-point number (`f32`) to be checked.
///
/// # Returns
///
/// Returns `true` if the given number is a positive signaling NaN, `false` otherwise.
///
/// # Details
///
/// This function internally converts the floating-point number into its raw
/// bits using [`f32::to_bits`] and delegates further processing to
/// [`f32_is_pos_snan_from_bits`].
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_pos_snan;
///
/// let positive_snan = f32::from_bits(0x7F80_0001); // Example bit pattern for a positive sNaN
/// assert!(f32_is_pos_snan(positive_snan));
///
/// let normal_f32 = 1.0;
/// assert!(!f32_is_pos_snan(normal_f32));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_pos_snan(f: f32) -> bool {
    f32_is_pos_snan_from_bits(f.to_bits())
}

/// Determines if a 32-bit floating-point number (`f32`), represented by its raw bits,
/// is a negative signaling NaN (sNaN).
///
/// # Arguments
///
/// * `bits` - The raw 32-bit representation of an `f32` number.
///
/// # Returns
///
/// Returns `true` if the `bits` represent a negative signaling NaN (sNaN), `false` otherwise.
///
/// # Details
///
/// - A signaling NaN (sNaN) is a special kind of NaN defined in IEEE 754 that is intended to
///   signal the invalid operation exception when used in computations.
/// - The function checks two conditions:
///   1. The `bits` correspond to a signaling NaN, determined by the helper function
///      [`f32_is_snan_from_bits`].
///   2. The sign bit (most significant bit) in the `bits` is set, indicating a negative value.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_snan_from_bits;
///
/// // Raw bit pattern for negative signaling NaN
/// let neg_snan_bits: u32 = 0xFF80_0001;
/// assert!(f32_is_neg_snan_from_bits(neg_snan_bits));
///
/// // Raw bit pattern for positive signaling NaN
/// let pos_snan_bits: u32 = 0x7F80_0001;
/// assert!(!f32_is_neg_snan_from_bits(pos_snan_bits));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_neg_snan_from_bits(bits: u32) -> bool {
    f32_is_snan_from_bits(bits) && (bits & FLT_SIGN_MASK) != 0
}

/// Checks if a given 32-bit floating-point number (`f32`) is a negative signaling NaN (sNaN).
///
/// A signaling NaN is a special kind of NaN (Not a Number) in the IEEE 754 floating-point
/// standard that is intended to raise exceptions when used in operations. This function
/// specifically checks for signaling NaNs that are negative.
///
/// # Arguments
///
/// * `f` - The `f32` value to check for being a negative signaling NaN.
///
/// # Returns
///
/// Returns `true` if the given `f32` value is a negative signaling NaN, `false` otherwise.
///
/// # Details
///
/// This function utilizes the bit representation of the floating-point number to determine
/// if it is a negative signaling NaN by calling the helper function [`f32_is_neg_snan_from_bits`].
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_neg_snan;
///
/// let negative_snan = f32::from_bits(0xFF80_0001); // Example of a negative sNaN
/// assert!(f32_is_neg_snan(negative_snan));
///
/// let positive_nan = f32::from_bits(0x7FC0_0000); // A positive quiet NaN
/// assert!(!f32_is_neg_snan(positive_nan));
///
/// let normal_float = 3.14_f32;
/// assert!(!f32_is_neg_snan(normal_float));
/// ```
///
/// # Note
///
/// This function assumes the IEEE 754 standard for floating-point representation.
#[must_use]
#[inline]
pub const fn f32_is_neg_snan(f: f32) -> bool {
    f32_is_neg_snan_from_bits(f.to_bits())
}

/// Determines if a 32-bit floating-point number, represented in its raw bit pattern, is subnormal.
///
/// A subnormal number in IEEE 754 floating-point representation has an exponent of 0
/// and a non-zero fraction. This function checks these conditions based on the raw `bits`
/// representation of the floating-point number.
///
/// # Arguments
///
/// * `bits` - A `u32` value representing the raw bits of a 32-bit floating-point number (`f32`).
///
/// # Returns
///
/// Returns `true` if the number is subnormal, `false` otherwise.
///
/// # Details
///
/// - `bits & FLT_ABS_MASK`: Masks out the sign bit to focus on the absolute value.
/// - `.wrapping_sub(1) < FLT_EXP_MASK.wrapping_sub(1)`: Verifies if the value is within the
///   subnormal range.
/// - `(bits & FLT_EXP_MASK) == 0`: Confirms that the exponent is zero.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_subnormal_from_bits;
///
/// let bits: u32 = 0x0000_0001; // Encodes a subnormal f32 value
/// assert!(f32_is_subnormal_from_bits(bits));
///
/// let bits: u32 = 0x3F80_0000; // Encodes a normalized f32 value (1.0)
/// assert!(!f32_is_subnormal_from_bits(bits));
/// ```
#[must_use]
#[inline]
pub const fn f32_is_subnormal_from_bits(bits: u32) -> bool {
    // Exponent is 0 and fraction is non-zero
    (bits & FLT_ABS_MASK).wrapping_sub(1) < FLT_EXP_MASK.wrapping_sub(1)
        && (bits & FLT_EXP_MASK) == 0
}

/// Determines whether a given 32-bit floating-point number (`f32`) is subnormal.
///
/// A subnormal (or denormal) number in floating-point arithmetic is a number
/// that is closer to zero than the smallest positive normalized floating-point number.
/// Subnormal numbers do not have an implicit leading 1 in their binary representation.
///
/// # Arguments
///
/// * `f` - A 32-bit floating-point number (`f32`) to check for the subnormal property.
///
/// # Returns
///
/// Returns `true` if the input `f` is a subnormal number, `false` otherwise.
///
/// # Details
///
/// This function delegates the actual computation to [`f32_is_subnormal_from_bits`],
/// using the bitwise representation of the floating-point number obtained via
/// [`f32::to_bits`].
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f32_is_subnormal;
///
/// assert!(f32_is_subnormal(1.0e-45)); // Smallest positive subnormal number
/// assert!(!f32_is_subnormal(1.0));    // Normalized number
/// ```
#[must_use]
#[inline]
pub const fn f32_is_subnormal(f: f32) -> bool {
    f32_is_subnormal_from_bits(f.to_bits())
}

/// Checks if the given bit pattern represents a NaN (Not a Number) value
/// for a 64-bit floating-point number (`f64`).
///
/// This function uses the bitwise representation of IEEE 754 `f64` to determine
/// if the provided `u64` bits correspond to a NaN value. It ignores the sign bit
/// and checks if the combination of exponent and mantissa bits matches the
/// criteria for NaN (exponent bits are all 1s, and the mantissa is non-zero).
///
/// # Arguments
///
/// * `bits` - A `u64` value representing the raw bits of an `f64` number.
///
/// # Returns
///
/// Returns `true` if the `bits` correspond to a NaN value, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_nan_from_bits;
///
/// assert!(f64_is_nan_from_bits(0x7FF8_0000_0000_0000));  // NaN
/// assert!(!f64_is_nan_from_bits(0x7FF0_0000_0000_0000)); // Infinity
/// assert!(!f64_is_nan_from_bits(0x0000_0000_0000_0000)); // Zero
/// ```
#[must_use]
#[inline]
pub const fn f64_is_nan_from_bits(bits: u64) -> bool {
    (bits & DBL_ABS_MASK) > DBL_EXP_MASK
}

/// Checks whether a given 64-bit floating-point number (`f64`) is NaN (Not-a-Number).
///
/// This function determines if the input `f` is a NaN value by converting its
/// underlying representation into raw bits (using [`f64::to_bits`]) and delegating the
/// check to the [`f64_is_nan_from_bits`] function.
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point number (`f64`) to check for NaN.
///
/// # Returns
///
/// Returns `true` if the input `f` is a NaN value, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_nan;
///
/// let num = 0.0 / 0.0; // Produces NaN
/// assert!(f64_is_nan(num));
///
/// let num = 42.0;
/// assert!(!f64_is_nan(num));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_nan(f: f64) -> bool {
    f64_is_nan_from_bits(f.to_bits())
}

/// Determines whether the given 64-bit representation of a floating-point number (`f64`)
/// is a quiet NaN (qNaN).
///
/// # Arguments
///
/// * `bits` - A `u64` representing the raw bit pattern of a 64-bit floating-point number (`f64`).
///
/// # Returns
///
/// Returns `true` if the bit pattern corresponds to a quiet NaN (qNaN), `false` otherwise.
///
/// # Details
///
/// - A NaN (Not a Number) in the IEEE 754 standard is represented by a bit pattern where:
///   - The exponent bits are all set to 1 (indicating infinity or NaN).
///   - At least one bit in the significand (mantissa) is set (distinguishing NaN from infinity).
/// - A quiet NaN (qNaN) specifically sets the most significant bit of the significand (the qNaN bit).
/// - [`DBL_ABS_MASK`] is used to mask out the sign bit, ensuring the comparison is based on the
///   absolute value description.
/// - [`DBL_EXP_MASK`] is used to check if the exponent bits are all set to 1.
/// - [`DBL_QNAN_BIT`] identifies the specific bit within the significand indicating a quiet NaN.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_qnan_from_bits;
///
/// let bits: u64 = 0x7FF8_0000_0000_0001; // Example: quiet NaN
/// assert!(f64_is_qnan_from_bits(bits));
///
/// let bits: u64 = 0x7FF0_0000_0000_0000; // Example: Infinity
/// assert!(!f64_is_qnan_from_bits(bits));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_qnan_from_bits(bits: u64) -> bool {
    (bits & DBL_ABS_MASK) > DBL_EXP_MASK && (bits & DBL_QNAN_BIT) != 0
}

/// Determines if a 64-bit floating-point value (`f64`) is a quiet NaN (qNaN).
///
/// A quiet NaN (qNaN) is a specific representation of NaN in the IEEE 754 standard,
/// designed to propagate through computations silently without raising exceptions.
///
/// This function converts the `f64` floating-point value into its raw bit representation
/// using the [`f64::to_bits`] method and delegates the check to the [`f64_is_qnan_from_bits`]
/// function.
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point value (`f64`) to check.
///
/// # Returns
///
/// Returns `true` if the given `f64` value is a quiet NaN, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_qnan;
///
/// assert!(f64_is_qnan(f64::NAN)); // Returns true for NaN values
/// assert!(!f64_is_qnan(42.0));    // Returns false for regular numbers
/// ```
#[must_use]
#[inline]
pub const fn f64_is_qnan(f: f64) -> bool {
    f64_is_qnan_from_bits(f.to_bits())
}

/// Determines whether a 64-bit floating-point number (`f64`), represented in its
/// bitwise form, is infinite.
///
/// # Arguments
///
/// * `bits` - The bitwise representation of an `f64` value.
///
/// # Returns
///
/// Returns `true` if the `f64` value represented by `bits` is infinite
/// (either positive or negative infinity), `false` otherwise.
///
/// # Details
///
/// The function checks the bitwise representation of an `f64` number using the
/// following steps:
/// - The constant [`DBL_ABS_MASK`] is applied to `bits` using a bitwise AND operation,
///   masking the sign bit and isolating the absolute value.
/// - The result is compared to [`DBL_EXP_MASK`], which represents the bit pattern
///   for infinity in IEEE 754 standard for double-precision floating-point format.
/// - If the masked value matches [`DBL_EXP_MASK`], the input represents an infinite
///   value and the function returns `true`. Otherwise, `false` is returned.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_infinite_from_bits;
///
/// const MY_FLOAT_BITS: u64 = 0x7FF0_0000_0000_0000; // Positive infinity
/// assert!(f64_is_infinite_from_bits(MY_FLOAT_BITS));
///
/// const NOT_INFINITY_BITS: u64 = 0x3FF0_0000_0000_0000; // 1.0
/// assert!(!f64_is_infinite_from_bits(NOT_INFINITY_BITS));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_infinite_from_bits(bits: u64) -> bool {
    (bits & DBL_ABS_MASK) == DBL_EXP_MASK
}

/// Checks whether a 64-bit floating-point number (`f64`) is infinite.
///
/// This function determines if the provided `f64` value represents either
/// positive infinity (`f64::INFINITY`) or negative infinity (`f64::NEG_INFINITY`)
/// by converting the floating-point value to its raw bit representation and
/// analyzing the underlying bits.
///
/// # Arguments
///
/// * `f` - The `f64` value to check for infinity.
///
/// # Returns
///
/// Returns `true` if the `f64` value is infinite (positive or negative infinity),
/// `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_infinite;
///
/// assert!(f64_is_infinite(f64::INFINITY));
/// assert!(f64_is_infinite(f64::NEG_INFINITY));
/// assert!(!f64_is_infinite(0.0));
/// assert!(!f64_is_infinite(1.0));
/// ```
///
/// # Note
///
/// This function indirectly calls [`f64_is_infinite_from_bits`], which determines
/// whether the bitwise representation of the `f64` indicates an infinite value.
#[must_use]
#[inline]
pub const fn f64_is_infinite(f: f64) -> bool {
    f64_is_infinite_from_bits(f.to_bits())
}

/// Determines if the given 64-bit representation of a floating-point number
/// corresponds to positive infinity (`+∞`).
///
/// This function compares the provided 64-bit unsigned integer (`bits`)
/// with the constant [`DBL_POS_INF`], which represents the bit pattern of positive
/// infinity in the IEEE 754 double-precision floating-point standard.
///
/// # Arguments
///
/// * `bits` - The 64-bit bit pattern to check.
///
/// # Returns
///
/// Returns `true` if `bits` matches the bit pattern of positive infinity, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_inf_from_bits;
///
/// const DBL_POS_INF: u64 = 0x7FF0_0000_0000_0000; // IEEE 754 positive infinity
/// assert!(f64_is_pos_inf_from_bits(DBL_POS_INF));
/// assert!(!f64_is_pos_inf_from_bits(0x7FE0_0000_0000_0000));
/// assert!(!f64_is_pos_inf_from_bits(0));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_pos_inf_from_bits(bits: u64) -> bool {
    bits == DBL_POS_INF
}

/// Determines if a given `f64` value is positive infinity (`+∞`).
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point number (`f64`) to be checked.
///
/// # Returns
///
/// Returns `true` if the input `f` is equal to positive infinity (`+∞`), `false` otherwise.
///
/// # Details
///
/// This function internally converts the `f64` value into its raw
/// bit representation using [`f64::to_bits`] and delegates the
/// computation to [`f64_is_pos_inf_from_bits`], which performs the
/// actual comparison against the bit pattern for positive infinity.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_inf;
///
/// assert!(f64_is_pos_inf(f64::INFINITY));     // Positive infinity
/// assert!(!f64_is_pos_inf(f64::NEG_INFINITY)); // Negative infinity
/// assert!(!f64_is_pos_inf(1.0));               // Regular finite number
/// assert!(!f64_is_pos_inf(f64::NAN));          // Not-a-Number (NaN)
/// ```
#[must_use]
#[inline]
pub const fn f64_is_pos_inf(f: f64) -> bool {
    f64_is_pos_inf_from_bits(f.to_bits())
}

/// Checks if the given 64-bit representation corresponds to negative infinity
/// in IEEE 754 floating-point format.
///
/// # Arguments
///
/// * `bits` - The 64-bit representation of an `f64` value.
///
/// # Returns
///
/// Returns `true` if the `bits` represent negative infinity, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_inf_from_bits;
///
/// const NEG_INF_BITS: u64 = 0xFFF0_0000_0000_0000; // IEEE 754 representation of -∞
/// assert!(f64_is_neg_inf_from_bits(NEG_INF_BITS));
///
/// const ZERO_BITS: u64 = 0x0000_0000_0000_0000; // IEEE 754 representation of 0.0
/// assert!(!f64_is_neg_inf_from_bits(ZERO_BITS));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_neg_inf_from_bits(bits: u64) -> bool {
    bits == DBL_NEG_INF
}

/// Checks if a given `f64` value is negative infinity.
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point number (`f64`) to evaluate.
///
/// # Returns
///
/// Returns `true` if the value of `f` represents negative infinity (`-∞`), `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_inf;
///
/// let value = -1.0_f64 / 0.0; // Generates negative infinity
/// assert!(f64_is_neg_inf(value));
///
/// let value = 1.0_f64 / 0.0; // Generates positive infinity
/// assert!(!f64_is_neg_inf(value));
///
/// let value = 0.0_f64; // Regular finite number
/// assert!(!f64_is_neg_inf(value));
/// ```
///
/// # Note
///
/// This function leverages the [`f64::to_bits`] method to obtain the raw bits
/// of the floating-point number and checks for negative infinity using the
/// helper function [`f64_is_neg_inf_from_bits`].
#[must_use]
#[inline]
pub const fn f64_is_neg_inf(f: f64) -> bool {
    f64_is_neg_inf_from_bits(f.to_bits())
}

/// Determines whether a given 64-bit representation of an `f64` floating-point number
/// corresponds to positive zero.
///
/// # Arguments
///
/// * `bits` - The raw bit representation of an `f64` floating-point number.
///
/// # Returns
///
/// Returns `true` if the given `bits` correspond to positive zero (`+0.0`),
/// `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_zero_from_bits;
///
/// assert!(f64_is_pos_zero_from_bits(0x0000_0000_0000_0000));  // Positive zero
/// assert!(!f64_is_pos_zero_from_bits(0x8000_0000_0000_0000)); // Negative zero
/// assert!(!f64_is_pos_zero_from_bits(0x3FF0_0000_0000_0000)); // 1.0
/// ```
#[must_use]
#[inline]
pub const fn f64_is_pos_zero_from_bits(bits: u64) -> bool {
    bits == DBL_POS_ZERO
}

/// Checks if a given `f64` value is a positive zero.
///
/// This function determines if the provided floating-point number (`f`)
/// is a positive zero (`+0.0`). In IEEE 754 floating-point representation,
/// positive zero is distinct from negative zero (`-0.0`), and this function
/// specifically checks for the positive variant.
///
/// It achieves this by converting the `f64` value to its raw bits using
/// [`f64::to_bits`] and delegating the check to the [`f64_is_pos_zero_from_bits`]
/// function.
///
/// # Arguments
///
/// * `f` - The floating-point value to check.
///
/// # Returns
///
/// Returns `true` if the value is positive zero (`+0.0`), `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_zero;
///
/// assert!(f64_is_pos_zero(0.0));
/// assert!(!f64_is_pos_zero(-0.0));
/// assert!(!f64_is_pos_zero(1.0));
/// assert!(!f64_is_pos_zero(-1.0));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_pos_zero(f: f64) -> bool {
    f64_is_pos_zero_from_bits(f.to_bits())
}

/// Checks if the provided `u64` bit pattern represents a negative zero
/// in IEEE 754 double-precision format.
///
/// # Arguments
///
/// * `bits` - The bit pattern to inspect.
///
/// # Returns
///
/// Returns `true` if the bit pattern corresponds to a negative zero (`-0.0`),
/// `false` otherwise.
///
/// # Details
///
/// In the IEEE 754 standard, negative zero is represented by a specific bit pattern:
/// - Sign bit: `1`
/// - Exponent bits: `0`
/// - Fraction (mantissa) bits: `0`
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_zero_from_bits;
///
/// const DBL_NEG_ZERO: u64 = 0x8000_0000_0000_0000;
/// assert!(f64_is_neg_zero_from_bits(DBL_NEG_ZERO)); // -0.0
///
/// const POS_ZERO_BITS: u64 = 0x0000_0000_0000_0000; // +0.0
/// assert!(!f64_is_neg_zero_from_bits(POS_ZERO_BITS));
///
/// const VALUE_BITS: u64 = 0x3FF0_0000_0000_0000; // 1.0
/// assert!(!f64_is_neg_zero_from_bits(VALUE_BITS));
/// ```
///
/// # See Also
///
/// - [`f64::to_bits`]: For getting the bit pattern of a floating-point number.
/// - [`f64::from_bits`]: For converting a bit pattern into a floating-point number.
#[must_use]
#[inline]
pub const fn f64_is_neg_zero_from_bits(bits: u64) -> bool {
    bits == DBL_NEG_ZERO
}

/// Checks if a given `f64` value is negative zero.
///
/// Negative zero in IEEE 754 floating-point representation is distinct from positive zero,
/// even though they are considered equal (`-0.0 == 0.0` evaluates to `true`). This function
/// specifically identifies negative zero without equating it to positive zero.
///
/// # Arguments
///
/// * `f` - An `f64` floating-point number to check.
///
/// # Returns
///
/// Returns `true` if the input represents negative zero, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_zero;
///
/// assert!(f64_is_neg_zero(-0.0));
/// assert!(!f64_is_neg_zero(0.0));
/// assert!(!f64_is_neg_zero(1.0));
/// assert!(!f64_is_neg_zero(-1.0));
/// ```
///
/// # Note
///
/// This function delegates the check to [`f64_is_neg_zero_from_bits`], which operates
/// on the bit representation of the floating-point number.
#[must_use]
#[inline]
pub const fn f64_is_neg_zero(f: f64) -> bool {
    f64_is_neg_zero_from_bits(f.to_bits())
}

/// Determines if a 64-bit floating-point number represented as `bits` is a positive quiet NaN.
///
/// A quiet NaN (Not-a-Number) is a special floating-point value defined in the IEEE 754 standard.
/// This function checks if the provided `bits` correspond to a quiet NaN and verifies that the
/// sign bit indicates a positive value.
///
/// # Arguments
///
/// * `bits` - The raw 64-bit representation of a floating-point number.
///
/// # Returns
///
/// Returns `true` if the `bits` represent a positive quiet NaN, `false` otherwise.
///
/// # Details
///
/// - The function relies on a helper function [`f64_is_qnan_from_bits`] to determine if `bits`
///   represent a quiet NaN.
/// - A positive value is identified by checking that the sign bit (based on [`DBL_SIGN_MASK`])
///   is set to zero.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_qnan_from_bits;
///
/// let bits: u64 = 0x7FF8_0000_0000_0000; // Positive quiet NaN
/// assert!(f64_is_pos_qnan_from_bits(bits));
///
/// let negative_nan_bits: u64 = 0xFFF8_0000_0000_0000; // Negative quiet NaN
/// assert!(!f64_is_pos_qnan_from_bits(negative_nan_bits));
///
/// let normal_bits: u64 = 0x3FE0_0000_0000_0000; // A normal positive double (0.5)
/// assert!(!f64_is_pos_qnan_from_bits(normal_bits));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_pos_qnan_from_bits(bits: u64) -> bool {
    f64_is_qnan_from_bits(bits) && (bits & DBL_SIGN_MASK) == 0
}

/// Checks if a given 64-bit floating-point number (`f64`) is a positive quiet NaN (qNaN).
///
/// A quiet NaN is a special value of `f64` used to represent the result of undefined or
/// unrepresentable operations such as `0.0 / 0.0`. Positive quiet NaNs have a specific bit
/// pattern where:
/// - The sign bit is 0 (indicating positivity).
/// - The exponent bits are all set to 1.
/// - At least the most significant bit of the mantissa is 1 (quiet NaN indicator).
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point (`f64`) number to check.
///
/// # Returns
///
/// Returns `true` if `f` is a positive quiet NaN, `false` otherwise.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_qnan;
///
/// let nan = f64::from_bits(0x7FF8_0000_0000_0000); // A positive quiet NaN
/// assert!(f64_is_pos_qnan(nan));
///
/// let normal = 1.23;
/// assert!(!f64_is_pos_qnan(normal));
///
/// let negative_nan = f64::from_bits(0xFFF8_0000_0000_0000); // A negative quiet NaN
/// assert!(!f64_is_pos_qnan(negative_nan));
/// ```
///
/// # Note
///
/// Internally, this function uses the helper function [`f64_is_pos_qnan_from_bits`]
/// which operates on the bit representation of the `f64` value.
///
/// # See Also
///
/// * [`f64::to_bits`] — Converts an `f64` value to its IEEE 754 bit pattern representation.
/// * [`f64_is_pos_qnan_from_bits`] — Checks for positive quiet NaN based on the bit pattern.
#[must_use]
#[inline]
pub const fn f64_is_pos_qnan(f: f64) -> bool {
    f64_is_pos_qnan_from_bits(f.to_bits())
}

/// Checks if the given `u64` bit pattern represents a negative quiet NaN (qNaN) value
/// in an `f64`.
///
/// A quiet NaN is a special type of NaN that does not signal exceptions or invalid operations.
/// This function determines if the provided bit pattern represents such a quiet NaN and if
/// it is negative.
///
/// # Arguments
///
/// * `bits` - The `u64` bit pattern to check. It is expected to be an `f64`'s raw representation.
///
/// # Returns
///
/// Returns `true` if the bit pattern represents a negative quiet NaN, `false` otherwise.
///
/// # Details
///
/// - A quiet NaN is identified by inspecting specific bits as defined by the IEEE 754
///   floating-point format.
/// - The sign of the NaN is determined by the sign bit ([`DBL_SIGN_MASK`]).
/// - This function relies on [`f64_is_qnan_from_bits`] to determine if the bit pattern
///   represents any quiet NaN.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_qnan_from_bits;
///
/// const QUIET_NAN_BITS: u64 = 0xFFF8_0000_0000_0001; // Negative quiet NaN
/// assert!(f64_is_neg_qnan_from_bits(QUIET_NAN_BITS));
///
/// const POS_QNAN_BITS: u64 = 0x7FF8_0000_0000_0001; // Positive quiet NaN
/// assert!(!f64_is_neg_qnan_from_bits(POS_QNAN_BITS));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_neg_qnan_from_bits(bits: u64) -> bool {
    f64_is_qnan_from_bits(bits) && (bits & DBL_SIGN_MASK) != 0
}

/// Determines if a given 64-bit floating-point number (`f64`) is a negative quiet NaN (qNaN).
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point number (`f64`) to be checked.
///
/// # Returns
///
/// Returns `true` if the floating-point number is a negative quiet NaN, `false` otherwise.
///
/// # Details
///
/// This function internally converts the floating-point number into its raw representation
/// using the [`f64::to_bits`] method and delegates the actual check to the function
/// [`f64_is_neg_qnan_from_bits`].
///
/// A quiet NaN is a NaN that does not raise a floating-point exception during use. The
/// "negative" refers to its sign bit being set.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_qnan;
///
/// let quiet_nan = f64::from_bits(0xFFF8_0000_0000_0000); // Negative quiet NaN
/// assert!(f64_is_neg_qnan(quiet_nan));
///
/// let normal_number = 42.0;
/// assert!(!f64_is_neg_qnan(normal_number));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_neg_qnan(f: f64) -> bool {
    f64_is_neg_qnan_from_bits(f.to_bits())
}

/// Determines if a 64-bit floating-point value, represented by its bit pattern,
/// is a positive signaling NaN (sNaN).
///
/// # Arguments
///
/// * `bits` - A `u64` representing the bit pattern of an `f64` value.
///
/// # Returns
///
/// Returns `true` if the bit pattern corresponds to a positive signaling NaN, `false` otherwise.
///
/// # Details
///
/// This function checks the following conditions to identify a positive signaling NaN:
/// 1. `(bits & DBL_ABS_MASK) > DBL_EXP_MASK`: Ensures the absolute value of the number is greater
///    than the maximum finite value, indicating the number is NaN (either signaling or quiet).
/// 2. `(bits & DBL_QNAN_BIT) == 0`: Verifies the NaN is a signaling NaN (not a quiet NaN) by
///    checking the absence of the "quiet NaN" bit.
/// 3. `(bits & DBL_SIGN_MASK) == 0`: Confirms the number is positive by checking that the sign
///    bit is not set.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_snan_from_bits;
///
/// let bits: u64 = 0x7FF0_0000_0000_0001; // Positive signaling NaN
/// assert!(f64_is_pos_snan_from_bits(bits));
///
/// let neg_snan: u64 = 0xFFF0_0000_0000_0001; // Negative signaling NaN
/// assert!(!f64_is_pos_snan_from_bits(neg_snan));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_pos_snan_from_bits(bits: u64) -> bool {
    (bits & DBL_ABS_MASK) > DBL_EXP_MASK
        && (bits & DBL_QNAN_BIT) == 0
        && (bits & DBL_SIGN_MASK) == 0
}

/// Checks if the given `f64` value is a positive signaling NaN (sNaN).
///
/// This function determines whether the input `f64` value is a positive signaling NaN
/// by converting it to its raw bit representation and delegating the actual check
/// to the helper function [`f64_is_pos_snan_from_bits`].
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point number (`f64`) to be checked.
///
/// # Returns
///
/// Returns `true` if the given `f64` value is a positive signaling NaN, `false` otherwise.
///
/// # Details
///
/// - Signaling NaNs (sNaNs) are a special class of NaN values designed to raise exceptions
///   when used in floating-point operations, as opposed to quiet NaNs (qNaNs), which do not.
/// - A positive sNaN has its sign bit set to `0`.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_pos_snan;
///
/// let x = f64::from_bits(0x7FF0_0000_0000_0001); // A positive signaling NaN
/// assert!(f64_is_pos_snan(x));
///
/// let y = 1.0; // A regular positive floating-point number
/// assert!(!f64_is_pos_snan(y));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_pos_snan(f: f64) -> bool {
    f64_is_pos_snan_from_bits(f.to_bits())
}

/// Determines if a 64-bit unsigned integer representing the bit pattern of an
/// `f64` floating-point number corresponds to a signaling negative NaN (sNaN).
///
/// # Arguments
///
/// * `bits` - The 64-bit representation of an `f64` floating-point number.
///
/// # Returns
///
/// Returns `true` if the bit pattern represents a signaling negative NaN (sNaN),
/// `false` otherwise.
///
/// # Details
///
/// A signaling NaN (sNaN) is differentiated from a quiet NaN (qNaN) by the state of
/// the most significant bit of the significand. For IEEE 754 double-precision
/// floating-point numbers:
/// - [`DBL_ABS_MASK`] isolates the absolute value of the number.
/// - [`DBL_EXP_MASK`] represents the exponent mask for NaN detection (all exponent bits set to 1).
/// - [`DBL_QNAN_BIT`] identifies whether the number is a quiet NaN (`1`) or signaling NaN (`0`).
/// - [`DBL_SIGN_MASK`] isolates the sign bit to check if the number is negative (`1`).
///
/// The function checks the following conditions:
/// 1. `(bits & DBL_ABS_MASK) > DBL_EXP_MASK`: Verifies if the bit pattern represents a NaN.
/// 2. `(bits & DBL_QNAN_BIT) == 0`: Ensures that the NaN is a signaling NaN (sNaN).
/// 3. `(bits & DBL_SIGN_MASK) != 0`: Confirms that the NaN is negative.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_snan_from_bits;
///
/// assert!(f64_is_neg_snan_from_bits(0xFFF0_0000_0000_0001)); // Negative signaling NaN
/// assert!(!f64_is_neg_snan_from_bits(0x7FF8_0000_0000_0000)); // Positive quiet NaN
/// ```
#[must_use]
#[inline]
pub const fn f64_is_neg_snan_from_bits(bits: u64) -> bool {
    (bits & DBL_ABS_MASK) > DBL_EXP_MASK
        && (bits & DBL_QNAN_BIT) == 0
        && (bits & DBL_SIGN_MASK) != 0
}

/// Checks if a given `f64` (64-bit floating-point number) is a negative signaling NaN (sNaN).
///
/// A signaling NaN is a special type of NaN (Not a Number) in floating-point arithmetic
/// that can generate exceptions when encountered in computations. This function determines
/// its signaling and negative properties based on its bit representation.
///
/// # Arguments
///
/// * `f` - The `f64` value to check.
///
/// # Returns
///
/// Returns `true` if the given `f64` is a negative signaling NaN, `false` otherwise.
///
/// # Details
///
/// This function utilizes the value-to-bit conversion provided by the [`f64::to_bits`] method
/// and delegates the actual sNaN checking to the [`f64_is_neg_snan_from_bits`] function.
/// The latter operates on the raw bit representation of the floating-point number.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_neg_snan;
///
/// let neg_snan = f64::from_bits(0xFFF0_0000_0000_0001); // Negative signaling NaN
/// assert!(f64_is_neg_snan(neg_snan));
///
/// let pos_qnan = f64::from_bits(0x7FF8_0000_0000_0000); // Positive quiet NaN
/// assert!(!f64_is_neg_snan(pos_qnan));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_neg_snan(f: f64) -> bool {
    f64_is_neg_snan_from_bits(f.to_bits())
}

/// Determines if a 64-bit floating-point number, represented by its raw bits,
/// is a subnormal (denormal) value.
///
/// A subnormal number in the IEEE 754 double-precision format is a non-zero
/// number where the exponent field is all zeroes, and the significand (mantissa)
/// contains the actual value.
///
/// # Arguments
///
/// * `bits` - The raw bit representation of the 64-bit floating-point number.
///
/// # Returns
///
/// Returns `true` if the number is subnormal, `false` otherwise.
///
/// # Details
///
/// The function performs the following checks:
/// 1. `(bits & DBL_ABS_MASK).wrapping_sub(1) < DBL_EXP_MASK.wrapping_sub(1)`: Checks that the
///    absolute magnitude of the number is less than or equal to the range of subnormal values.
/// 2. `(bits & DBL_EXP_MASK) == 0`: Ensures the exponent field is all zeros, which is a
///    necessary condition for subnormality.
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_subnormal_from_bits;
///
/// let bits: u64 = 0x0008_0000_0000_0000; // Example raw bits for a subnormal value
/// assert!(f64_is_subnormal_from_bits(bits));
///
/// let bits: u64 = 0x3FF0_0000_0000_0000; // Example raw bits for a normal value (1.0)
/// assert!(!f64_is_subnormal_from_bits(bits));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_subnormal_from_bits(bits: u64) -> bool {
    (bits & DBL_ABS_MASK).wrapping_sub(1) < DBL_EXP_MASK.wrapping_sub(1)
        && (bits & DBL_EXP_MASK) == 0
}

/// Determines if a given `f64` floating-point number is a subnormal (denormal) value.
///
/// Subnormal values are non-zero numbers that are smaller in magnitude
/// than the smallest positive normalized floating-point number. These numbers
/// use a special encoding in the IEEE 754 standard and can represent very
/// small values at the cost of less precision.
///
/// # Arguments
///
/// * `f` - A 64-bit floating-point number (`f64`) to test for subnormality.
///
/// # Returns
///
/// Returns `true` if the input number `f` is subnormal, `false` otherwise
/// (including if `f` is zero, infinity, or NaN).
///
/// # Details
///
/// This function relies on the [`f64_is_subnormal_from_bits`] function,
/// which performs the subnormal check based on the raw bit pattern
/// of the floating-point number obtained using [`f64::to_bits`].
///
/// # Examples
///
/// ```
/// use ribm::helpers::classify::f64_is_subnormal;
///
/// let x = 1.0e-310; // A subnormal value
/// assert!(f64_is_subnormal(x));
///
/// let y = 0.5; // A normalized value
/// assert!(!f64_is_subnormal(y));
///
/// let z = 0.0; // Zero is not considered subnormal
/// assert!(!f64_is_subnormal(z));
/// ```
#[must_use]
#[inline]
pub const fn f64_is_subnormal(f: f64) -> bool {
    f64_is_subnormal_from_bits(f.to_bits())
}
