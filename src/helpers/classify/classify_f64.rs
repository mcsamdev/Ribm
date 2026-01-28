//! The file containing classification of 64 bit floating point numbers.

use crate::helpers::consts::{
    DBL_ABS_MASK, DBL_EXP_MASK, DBL_NEG_INF, DBL_NEG_ZERO, DBL_POS_INF, DBL_POS_ZERO, DBL_QNAN_BIT,
    DBL_SIGN_MASK,
};

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
