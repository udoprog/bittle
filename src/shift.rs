//! Traits for dealing with shift ordering.

use crate::number::Number;

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::Shl {}
    impl Sealed for super::Shr {}
}

/// Trait governing how a shift operation is performed over a number.
pub trait Shift: 'static + self::sealed::Sealed {
    /// Generate an overflowing mask for the given index.
    fn mask<T>(index: u32) -> T
    where
        T: Number;

    /// Generate a reverse overflowing mask at the given index, that is at
    /// the `BITS - index - 1` bit location.
    fn mask_rev<T>(index: u32) -> T
    where
        T: Number;

    /// Count the number of "leading" ones.
    fn ones<T>(value: T) -> u32
    where
        T: Number;

    /// Count the number of "trailing" ones.
    fn ones_rev<T>(value: T) -> u32
    where
        T: Number;

    /// Count the number of "leading" zeros.
    fn zeros<T>(value: T) -> u32
    where
        T: Number;

    /// Count the number of "trailing" zeros.
    fn zeros_rev<T>(value: T) -> u32
    where
        T: Number;
}

/// Shift-left indexing for bit sets.
///
/// This can be used in combination with methods such as
/// [`Bits::test_bit_with`].
///
/// Shift-left indexing is constructed increasingly from right to left for
/// individual primitives, such as the following [`u8`] literal:
///
/// ```text
/// 0b0010_0010u8
///     ^    ^- index 1
///     '------ index 5
/// ```
///
/// Arrays are treated the same as expected where the index grows from smallest
/// to largest address, but each interior primitive is indexed using shift left
/// indexing:
///
/// ```text
///  0 --------- 8  8 -------- 15
/// [0b0010_0010u8, 0b1000_0000u8]
///      ^    ^       ^- index 15
///      |    '--------- index 1
///      '-------------- index 5
/// ```
///
/// [`Bits::test_bit_with`]: crate::Bits::test_bit_with
#[non_exhaustive]
pub struct Shl;

impl Shift for Shl {
    #[inline]
    fn mask<T>(index: u32) -> T
    where
        T: Number,
    {
        T::mask(index)
    }

    #[inline]
    fn mask_rev<T>(index: u32) -> T
    where
        T: Number,
    {
        T::mask_rev(index)
    }

    #[inline]
    fn ones<T>(value: T) -> u32
    where
        T: Number,
    {
        value.ones()
    }

    #[inline]
    fn ones_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.ones_rev()
    }

    #[inline]
    fn zeros<T>(value: T) -> u32
    where
        T: Number,
    {
        value.zeros()
    }

    #[inline]
    fn zeros_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.zeros_rev()
    }
}

/// Shift-right indexing for bit sets.
///
/// This can be used in combination with methods such as
/// [`Bits::test_bit_with`].
///
/// Shift-right indexing is constructed increasingly from left to right for
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
/// [`Bits::test_bit_with`]: crate::Bits::test_bit_with
#[non_exhaustive]
pub struct Shr;

impl Shift for Shr {
    #[inline]
    fn mask<T>(index: u32) -> T
    where
        T: Number,
    {
        T::mask_rev(index)
    }

    #[inline]
    fn mask_rev<T>(index: u32) -> T
    where
        T: Number,
    {
        T::mask(index)
    }

    #[inline]
    fn ones<T>(value: T) -> u32
    where
        T: Number,
    {
        value.ones_rev()
    }

    #[inline]
    fn ones_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.ones()
    }

    #[inline]
    fn zeros<T>(value: T) -> u32
    where
        T: Number,
    {
        value.zeros_rev()
    }

    #[inline]
    fn zeros_rev<T>(value: T) -> u32
    where
        T: Number,
    {
        value.zeros()
    }
}

/// The default shift index in use.
#[allow(clippy::module_name_repetitions)]
pub type DefaultShift = Shl;
