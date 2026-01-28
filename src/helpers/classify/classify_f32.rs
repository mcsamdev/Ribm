//! The file containing classification of 32 bit floating point numbers.

use crate::helpers::consts::{
    FLT_ABS_MASK, FLT_EXP_MASK, FLT_NEG_INF, FLT_NEG_ZERO, FLT_POS_INF, FLT_POS_ZERO, FLT_QNAN_BIT,
    FLT_SIGN_MASK,
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
