//! Traits for dealing with bitset endianness.
//!
//! Endianness typically refers to the order in which bytes are in memory, but
//! here the concept refers to the order in which bits are addressed when you
//! consider the binary literal of a primitive.
//!
//! * [`BigEndian`] where the bit furthest to the left refers to the highest
//!   index.
//! * [`LittleEndian`] where the bit furthest to the left refers to the lowest
//!   index.

#![allow(clippy::module_name_repetitions)]

use crate::number::Number;

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::BigEndian {}
    impl Sealed for super::LittleEndian {}
}

/// Trait governing endian-dependent operations for a primitive.
pub trait Endian: self::sealed::Sealed {
    #[doc(hidden)]
    fn mask<T>(index: u32) -> T
    where
        T: Number;

    #[doc(hidden)]
    fn mask_rev<T>(index: u32) -> T
    where
        T: Number;

    #[doc(hidden)]
    fn ones<T>(value: T) -> u32
    where
        T: Number;

    #[doc(hidden)]
    fn ones_rev<T>(value: T) -> u32
    where
        T: Number;

    #[doc(hidden)]
    fn zeros<T>(value: T) -> u32
    where
        T: Number;

    #[doc(hidden)]
    fn zeros_rev<T>(value: T) -> u32
    where
        T: Number;
}

/// Big-endian indexing for bit sets.
///
/// This can be used in combination with methods such as [`Bits::test_bit_in`].
///
/// Big-endian indexing is constructed increasingly from right to left for
/// individual primitives, such as the following [`u8`] literal:
///
/// ```text
/// 0b0010_0010u8
///     ^    ^- index 1
///     '------ index 5
/// ```
///
/// Arrays are treated the same as expected where the index grows from smallest
/// to largest address, but each interior primitive is indexed in big endian
/// ordering.
///
/// ```text
///  0 --------- 8  8 -------- 15
/// [0b0010_0010u8, 0b1000_0000u8]
///      ^    ^       ^- index 15
///      |    '--------- index 1
///      '-------------- index 5
/// ```
///
/// [`Bits::test_bit_in`]: crate::Bits::test_bit_in
#[non_exhaustive]
pub struct BigEndian;

impl Endian for BigEndian {
    #[inline]
    fn mask<T>(index: u32) -> T
    where
        T: Number,
    {
        T::BIT_RIGHT.wrapping_shl(index)
    }

    #[inline]
    fn mask_rev<T>(index: u32) -> T
    where
        T: Number,
    {
        T::BIT_LEFT.wrapping_shr(index)
    }

    #[inline]
    fn ones<T>(value: T) -> u32
    where
        T: Number,
    {
        value.trailing_ones()
    }

    #[inline]
    fn ones_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.leading_ones()
    }

    #[inline]
    fn zeros<T>(value: T) -> u32
    where
        T: Number,
    {
        value.trailing_zeros()
    }

    #[inline]
    fn zeros_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.leading_zeros()
    }
}

/// Little-endian indexing for bit sets.
///
/// This can be used in combination with methods such as [`Bits::test_bit_in`].
///
/// Little-endian indexing is constructed increasingly from left to right for
/// individual primitives, such as the following [`u8`] literal:
///
/// ```text
/// 0b0010_0010u8
///     ^    ^- index 6
///     '------ index 2
/// ```
///
/// Arrays are treated the same as expected where the index grows from smallest
/// to largest address:
///
/// ```text
///  0 --------- 8  8 -------- 15
/// [0b0010_0010u8, 0b1000_0000u8]
///      ^    ^       ^- index 8
///      |    '--------- index 6
///      '-------------- index 2
/// ```
///
/// [`Bits::test_bit_in`]: crate::Bits::test_bit_in
#[non_exhaustive]
pub struct LittleEndian;

impl Endian for LittleEndian {
    #[inline]
    fn mask<T>(index: u32) -> T
    where
        T: Number,
    {
        T::BIT_LEFT.wrapping_shr(index)
    }

    #[inline]
    fn mask_rev<T>(index: u32) -> T
    where
        T: Number,
    {
        T::BIT_RIGHT.wrapping_shl(index)
    }

    #[inline]
    fn ones<T>(value: T) -> u32
    where
        T: Number,
    {
        value.leading_ones()
    }

    #[inline]
    fn ones_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.trailing_ones()
    }

    #[inline]
    fn zeros<T>(value: T) -> u32
    where
        T: Number,
    {
        value.leading_zeros()
    }

    #[inline]
    fn zeros_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.trailing_ones()
    }
}

/// The default endianness to use.
pub type DefaultEndian = BigEndian;
