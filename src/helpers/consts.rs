//! Floating point helper constants as unsigned integers.
//!
//! These constants provide bitmasks, shift values, and special bit patterns
//! used for manipulating IEEE 754 floating-point numbers (`f32` and `f64`)
//! directly via their integer representations.

/// Bitmask to isolate the sign bit of an `f32` (bit 31).
pub const FLT_SIGN_MASK: u32 = 0x8000_0000;
/// Bitmask to isolate the exponent bits of an `f32` (bits 23-30).
pub const FLT_EXP_MASK: u32 = 0x7F80_0000;
/// Bitmask to isolate the fraction (mantissa) bits of an `f32` (bits 0-22).
pub const FLT_FRAC_MASK: u32 = 0x007F_FFFF;
/// Bitmask to clear the sign bit, resulting in the absolute value.
pub const FLT_ABS_MASK: u32 = 0x7FFF_FFFF;
/// The bias value for the exponent of an `f32` (127).
pub const FLT_EXP_BIAS: u32 = 0x0000_007F;
/// Bit pattern representing positive infinity for `f32`.
pub const FLT_POS_INF: u32 = 0x7F80_0000;
/// Bit pattern representing negative infinity for `f32`.
pub const FLT_NEG_INF: u32 = 0xFF80_0000;
/// Bit pattern representing a canonical Quiet NaN (qNaN) for `f32`.
pub const FLT_QNAN: u32 = 0x7FC0_0000;
/// Bit pattern representing positive zero (`+0.0`) for `f32`.
pub const FLT_POS_ZERO: u32 = 0x0000_0000;
/// Bit pattern representing negative zero (`-0.0`) for `f32`.
pub const FLT_NEG_ZERO: u32 = 0x8000_0000;
/// Number of bits to shift to align the sign bit to the least significant position.
pub const FLT_SIGN_SHIFT: u32 = 0x0000_001F;
/// Number of bits to shift to align the exponent to the least significant position.
pub const FLT_EXP_SHIFT: u32 = 0x0000_0017;
/// Number of bits to shift to align the fraction to the least significant position (0).
pub const FLT_FRAC_SHIFT: u32 = 0x0000_0000;
/// The number of bits allocated for the exponent in `f32` (8 bits).
pub const FLT_EXP_BITS: u32 = 0x0000_0008;
/// The number of bits allocated for the fraction in `f32` (23 bits).
pub const FLT_FRAC_BITS: u32 = 0x0000_0017;
/// The offset used to calculate the unbiased exponent (equal to the bias).
pub const FLT_UNBIASED_EXP_OFFSET: u32 = FLT_EXP_BIAS;
/// The specific bit within the mantissa that distinguishes a Quiet NaN from a Signaling NaN.
pub const FLT_QNAN_BIT: u32 = 0x0040_0000;
/// The value of the sign bit representing a positive number (unshifted).
pub const FLT_SIGN_POS: u32 = 0x0000_0000;
/// The value of the sign bit representing a negative number (shifted to LSB).
pub const FLT_SIGN_NEG: u32 = 0x0000_0001;
/// The value of the exponent field when all bits are set to 1 (unshifted).
pub const FLT_EXP_ALL_ONES: u32 = 0x0000_00FF;
/// The value of the exponent field when all bits are set to 0.
pub const FLT_EXP_ALL_ZERO: u32 = 0x0000_0000;
/// The value of the fraction field when all bits are set to 0.
pub const FLT_FRAC_ZERO: u32 = 0x0000_0000;

/// Bitmask to isolate the sign bit of an `f64` (bit 63).
pub const DBL_SIGN_MASK: u64 = 0x8000_0000_0000_0000;
/// Bitmask to isolate the exponent bits of an `f64` (bits 52-62).
pub const DBL_EXP_MASK: u64 = 0x7FF0_0000_0000_0000;
/// Bitmask to isolate the fraction (mantissa) bits of an `f64` (bits 0-51).
pub const DBL_FRAC_MASK: u64 = 0x000F_FFFF_FFFF_FFFF;
/// Bitmask to clear the sign bit, resulting in the absolute value.
pub const DBL_ABS_MASK: u64 = 0x7FFF_FFFF_FFFF_FFFF;
/// The bias value for the exponent of an `f64` (1023).
pub const DBL_EXP_BIAS: u64 = 0x0000_0000_0000_03FF;
/// Bit pattern representing positive infinity for `f64`.
pub const DBL_POS_INF: u64 = 0x7FF0_0000_0000_0000;
/// Bit pattern representing negative infinity for `f64`.
pub const DBL_NEG_INF: u64 = 0xFFF0_0000_0000_0000;
/// Bit pattern representing a canonical Quiet NaN (qNaN) for `f64`.
pub const DBL_QNAN: u64 = 0x7FF8_0000_0000_0000;
/// Bit pattern representing positive zero (`+0.0`) for `f64`.
pub const DBL_POS_ZERO: u64 = 0x0000_0000_0000_0000;
/// Bit pattern representing negative zero (`-0.0`) for `f64`.
pub const DBL_NEG_ZERO: u64 = 0x8000_0000_0000_0000;
/// Number of bits to shift to align the sign bit to the least significant position.
pub const DBL_SIGN_SHIFT: u32 = 0x0000_003F;
/// Number of bits to shift to align the exponent to the least significant position.
pub const DBL_EXP_SHIFT: u32 = 0x0000_0034;
/// Number of bits to shift to align the fraction to the least significant position (0).
pub const DBL_FRAC_SHIFT: u32 = 0x0000_0000;
/// The number of bits allocated for the exponent in `f64` (11 bits).
pub const DBL_EXP_BITS: u32 = 0x0000_000B;
/// The number of bits allocated for the fraction in `f64` (52 bits).
pub const DBL_FRAC_BITS: u32 = 0x0000_0034;
/// The offset used to calculate the unbiased exponent (equal to the bias).
pub const DBL_UNBIASED_EXP_OFFSET: u64 = DBL_EXP_BIAS;
/// The specific bit within the mantissa that distinguishes a Quiet NaN from a Signaling NaN.
pub const DBL_QNAN_BIT: u64 = 0x0008_0000_0000_0000;
/// The value of the sign bit representing a positive number (unshifted).
pub const DBL_SIGN_POS: u64 = 0x0000_0000_0000_0000;
/// The value of the sign bit representing a negative number (shifted to LSB).
pub const DBL_SIGN_NEG: u64 = 0x0000_0000_0000_0001;
/// The value of the exponent field when all bits are set to 1 (unshifted).
pub const DBL_EXP_ALL_ONES: u64 = 0x0000_0000_0000_07FF;
/// The value of the exponent field when all bits are set to 0.
pub const DBL_EXP_ALL_ZERO: u64 = 0x0000_0000_0000_0000;
/// The value of the fraction field when all bits are set to 0.
pub const DBL_FRAC_ZERO: u64 = 0x0000_0000_0000_0000;
