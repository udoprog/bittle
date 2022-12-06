//! [Bits] implementation and associated types for numbers.

use crate::bits::{Bits, OwnedBits};

/// Basic numerical trait for the plumbing of a bit set. This ensures that only
/// primitive types can be used as the basis of a bit set backed by an array,
/// like `[u64; 4]` and not `[[u32; 2]; 4]`.
pub trait Number: Copy {
    /// Number of trailing zeros.
    fn trailing_zeros(self) -> u32;

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
            fn count_ones(self) -> u32 {
                <Self>::count_ones(self)
            }
        }

        impl Bits for $ty {
            type IterBits<'a> = IterBits<Self> where Self: 'a;

            #[inline]
            fn is_empty(&self) -> bool {
                *self == Self::EMPTY
            }

            #[inline]
            fn is_full(&self) -> bool {
                *self == Self::FULL
            }

            #[inline]
            fn test(&self, index: u32) -> bool {
                if index > <$ty>::BITS {
                    return false;
                }

                (*self & (1 << index)) != 0
            }

            #[inline]
            fn set(&mut self, index: u32) {
                if index <= <$ty>::BITS {
                    *self |= 1 << index;
                }
            }

            #[inline]
            fn unset(&mut self, index: u32) {
                if index <= <$ty>::BITS {
                    *self &= !(1 << index);
                }
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
            fn clear(&mut self) {
                *self = Self::EMPTY;
            }

            #[inline]
            fn iter_bits(&self) -> Self::IterBits<'_> {
                IterBits { bits: *self }
            }
        }

        impl OwnedBits for $ty {
            const BITS: u32 = (core::mem::size_of::<$ty>() * 8) as u32;
            const EMPTY: Self = 0;
            const FULL: Self = !0;

            type IntoBits = IterBits<Self>;

            #[inline]
            fn empty() -> Self {
                Self::EMPTY
            }

            #[inline]
            fn full() -> Self {
                Self::FULL
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
            fn into_bits(self) -> Self::IntoBits {
                IterBits { bits: self }
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

/// An iterator over the bits of a primitive number.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct IterBits<T>
where
    T: Number,
{
    bits: T,
}

impl<T> Iterator for IterBits<T>
where
    T: OwnedBits + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.is_empty() {
            return None;
        }

        let index = self.bits.trailing_zeros();
        self.bits.unset(index);
        Some(index)
    }
}
