//! [Bits] associated types for primitive numbers.

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;

mod sealed {
    /// Basic numerical trait for the plumbing of a bit set. This ensures that only
    /// primitive types can be used as the basis of a bit set backed by an array,
    /// like `[u64; 4]` and not `[[u32; 2]; 4]`.
    pub trait Number: Copy {
        /// Turn an index into a mask.
        fn mask(index: u32) -> Self;

        /// Turn an index into a reverse mask.
        fn mask_rev(index: u32) -> Self;

        /// Number of leading zeros.
        fn leading_zeros(self) -> u32;

        /// Number of trailing zeros.
        fn trailing_zeros(self) -> u32;

        /// Number of leading ones.
        fn leading_ones(self) -> u32;

        /// Number of trailing ones.
        fn trailing_ones(self) -> u32;

        /// Count number of ones.
        fn count_ones(self) -> u32;

        /// Count number of zeros.
        fn count_zeros(self) -> u32;

        /// Set reverse bit.
        fn set_bit_rev(&mut self, index: u32);

        /// Clear reverse bit.
        fn clear_bit_rev(&mut self, index: u32);
    }
}

pub(crate) use self::sealed::Number;

macro_rules! number {
    ($ty:ty) => {
        impl Number for $ty {
            #[inline]
            fn mask(index: u32) -> Self {
                const ONE: $ty = !(<$ty>::MAX >> 1);
                ONE.wrapping_shr(index)
            }

            #[inline]
            fn mask_rev(index: u32) -> Self {
                const ONE: $ty = 1 as $ty;
                ONE.wrapping_shl(index)
            }

            #[inline]
            fn leading_zeros(self) -> u32 {
                <Self>::leading_zeros(self)
            }

            #[inline]
            fn trailing_zeros(self) -> u32 {
                <Self>::trailing_zeros(self)
            }

            #[inline]
            fn leading_ones(self) -> u32 {
                <Self>::leading_ones(self)
            }

            #[inline]
            fn trailing_ones(self) -> u32 {
                <Self>::trailing_ones(self)
            }

            #[inline]
            fn count_ones(self) -> u32 {
                <Self>::count_ones(self)
            }

            #[inline]
            fn count_zeros(self) -> u32 {
                <Self>::count_zeros(self)
            }

            #[inline]
            fn set_bit_rev(&mut self, index: u32) {
                *self |= <$ty>::mask_rev(index);
            }

            #[inline]
            fn clear_bit_rev(&mut self, index: u32) {
                *self &= !<$ty>::mask_rev(index);
            }
        }

        impl crate::bits::Sealed for $ty {}

        impl Bits for $ty {
            type IterOnes<'a> = IterOnes<Self> where Self: 'a;
            type IterZeros<'a> = IterZeros<Self> where Self: 'a;

            #[inline]
            fn count_ones(&self) -> u32 {
                <$ty>::count_ones(*self)
            }

            #[inline]
            fn bits_capacity(&self) -> u32 {
                Self::BITS
            }

            #[inline]
            fn all_zeros(&self) -> bool {
                *self == Self::ZEROS
            }

            #[inline]
            fn all_ones(&self) -> bool {
                *self == Self::ONES
            }

            #[inline]
            fn test_bit(&self, index: u32) -> bool {
                *self & <$ty>::mask(index) != 0
            }

            #[inline]
            fn iter_ones(&self) -> Self::IterOnes<'_> {
                IterOnes { bits: *self }
            }

            #[inline]
            fn iter_zeros(&self) -> Self::IterZeros<'_> {
                IterZeros { bits: *self }
            }
        }

        impl BitsMut for $ty {
            #[inline]
            fn set_bit(&mut self, index: u32) {
                *self |= <$ty>::mask(index);
            }

            #[inline]
            fn clear_bit(&mut self, index: u32) {
                *self &= !<$ty>::mask(index);
            }

            #[inline]
            fn union_assign(&mut self, other: &Self) {
                *self |= other;
            }

            #[inline]
            fn conjunction_assign(&mut self, other: &Self) {
                *self &= other;
            }

            #[inline]
            fn difference_assign(&mut self, other: &Self) {
                *self = other & !*self;
            }

            #[inline]
            fn symmetric_difference_assign(&mut self, other: &Self) {
                *self ^= other;
            }

            #[inline]
            fn clear_bits(&mut self) {
                *self = Self::ZEROS;
            }
        }

        impl BitsOwned for $ty {
            const BITS: u32 = (core::mem::size_of::<$ty>() * 8) as u32;
            const ZEROS: Self = 0;
            const ONES: Self = !0;

            type IntoIterOnes = IterOnes<Self>;
            type IntoIterZeros = IterZeros<Self>;

            #[inline]
            fn zeros() -> Self {
                Self::ZEROS
            }

            #[inline]
            fn ones() -> Self {
                Self::ONES
            }

            #[inline]
            fn with_bit(self, bit: u32) -> Self {
                self | <$ty>::mask(bit)
            }

            #[inline]
            fn without_bit(self, bit: u32) -> Self {
                self & !<$ty>::mask(bit)
            }

            #[inline]
            fn union(self, other: Self) -> Self {
                self | other
            }

            #[inline]
            fn conjunction(self, other: Self) -> Self {
                self & other
            }

            #[inline]
            fn difference(self, other: Self) -> Self {
                !self & other
            }

            #[inline]
            fn symmetric_difference(self, other: Self) -> Self {
                self ^ other
            }

            #[inline]
            fn into_iter_ones(self) -> Self::IntoIterOnes {
                IterOnes { bits: self }
            }

            #[inline]
            fn into_iter_zeros(self) -> Self::IntoIterZeros {
                IterZeros { bits: self }
            }
        }
    };
}

number!(usize);
number!(isize);
number!(u8);
number!(i8);
number!(u16);
number!(i16);
number!(u32);
number!(i32);
number!(u64);
number!(i64);
number!(u128);
number!(i128);

/// An iterator over ones in a primitive number.
#[derive(Clone)]
#[repr(transparent)]
pub struct IterOnes<T>
where
    T: Number,
{
    bits: T,
}

impl<T> Iterator for IterOnes<T>
where
    T: BitsOwned + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.all_zeros() {
            return None;
        }

        let index = self.bits.leading_zeros();
        self.bits.clear_bit(index);
        Some(index)
    }
}

/// Double ended iterator over ones.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
/// assert!(0b10001000u8.iter_ones().rev().eq([4, 0]));
/// ```
impl<T> DoubleEndedIterator for IterOnes<T>
where
    T: BitsOwned + Number,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits.all_zeros() {
            return None;
        }

        let index = self.bits.trailing_zeros();
        self.bits.clear_bit_rev(index);
        Some(T::BITS - index - 1)
    }
}

impl<T> ExactSizeIterator for IterOnes<T>
where
    T: BitsOwned + Number,
{
    #[inline]
    fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }
}

/// An iterator over zeros in a primitive number.
#[derive(Clone)]
#[repr(transparent)]
pub struct IterZeros<T> {
    bits: T,
}

impl<T> Iterator for IterZeros<T>
where
    T: BitsMut + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.all_ones() {
            return None;
        }

        let index = self.bits.leading_ones();
        self.bits.set_bit(index);
        Some(index)
    }
}

impl<T> ExactSizeIterator for IterZeros<T>
where
    T: BitsMut + Number,
{
    #[inline]
    fn len(&self) -> usize {
        self.bits.count_zeros() as usize
    }
}

/// Double ended iterator over zeros.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
/// assert!(0b10001000u8.iter_zeros().rev().eq([7, 6, 5, 3, 2, 1]));
/// ```
impl<T> DoubleEndedIterator for IterZeros<T>
where
    T: BitsOwned + Number,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits.all_ones() {
            return None;
        }

        let index = self.bits.trailing_ones();
        self.bits.set_bit_rev(index);
        Some(T::BITS - index - 1)
    }
}
