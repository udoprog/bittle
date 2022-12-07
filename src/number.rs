//! [Bits] implementation and associated types for numbers.

use crate::bits::Bits;
use crate::owned_bits::OwnedBits;

/// Basic numerical trait for the plumbing of a bit set. This ensures that only
/// primitive types can be used as the basis of a bit set backed by an array,
/// like `[u64; 4]` and not `[[u32; 2]; 4]`.
pub trait Number: Copy {
    /// Number of trailing zeros.
    fn trailing_zeros(self) -> u32;

    /// Number of trailing ones.
    fn trailing_ones(self) -> u32;

    /// Count number of ones.
    fn count_ones(self) -> u32;
}

macro_rules! number {
    ($ty:ty) => {
        impl Number for $ty {
            #[inline]
            fn trailing_zeros(self) -> u32 {
                <Self>::trailing_zeros(self)
            }

            #[inline]
            fn trailing_ones(self) -> u32 {
                <Self>::trailing_ones(self)
            }

            #[inline]
            fn count_ones(self) -> u32 {
                <Self>::count_ones(self)
            }
        }

        impl Bits for $ty {
            type IterOnes<'a> = IterOnes<Self> where Self: 'a;
            type IterZeros<'a> = IterZeros<Self> where Self: 'a;

            #[inline]
            fn bits_len(&self) -> u32 {
                <$ty>::count_ones(*self)
            }

            #[inline]
            fn bits_capacity(&self) -> u32 {
                Self::BITS
            }

            #[inline]
            fn is_zeros(&self) -> bool {
                *self == Self::ZEROS
            }

            #[inline]
            fn is_ones(&self) -> bool {
                *self == Self::ONES
            }

            #[inline]
            fn bit_test(&self, index: u32) -> bool {
                const ONE: $ty = 1;
                (*self & ONE.wrapping_shl(index)) != 0
            }

            #[inline]
            fn bit_set(&mut self, index: u32) {
                const ONE: $ty = 1;
                *self |= ONE.wrapping_shl(index);
            }

            #[inline]
            fn bit_clear(&mut self, index: u32) {
                const ONE: $ty = 1;
                *self &= !ONE.wrapping_shl(index);
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
            fn bits_clear(&mut self) {
                *self = Self::ZEROS;
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

        impl OwnedBits for $ty {
            const BITS: u32 = (core::mem::size_of::<$ty>() * 8) as u32;
            const ZEROS: Self = 0;
            const ONES: Self = !0;

            type IntoIterOnes = IterOnes<Self>;

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
                const ONE: $ty = 1;
                self | ONE.wrapping_shl(bit)
            }

            #[inline]
            fn without_bit(self, bit: u32) -> Self {
                const ONE: $ty = 1;
                self & !ONE.wrapping_shl(bit)
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
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct IterOnes<T>
where
    T: Number,
{
    bits: T,
}

impl<T> Iterator for IterOnes<T>
where
    T: OwnedBits + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.is_zeros() {
            return None;
        }

        let index = self.bits.trailing_zeros();
        self.bits.bit_clear(index);
        Some(index)
    }
}

/// An iterator over zeros in a primitive number.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct IterZeros<T>
where
    T: Number,
{
    bits: T,
}

impl<T> Iterator for IterZeros<T>
where
    T: OwnedBits + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.is_ones() {
            return None;
        }

        let index = self.bits.trailing_ones();
        self.bits.bit_set(index);
        Some(index)
    }
}
