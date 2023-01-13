//! [Bits] associated types for primitive numbers.

use core::marker::PhantomData;

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::shift::{DefaultShift, Shift};

mod sealed {
    use crate::shift::Shift;

    /// Basic numerical trait for the plumbing of a bit set. This ensures that only
    /// primitive types can be used as the basis of a bit set backed by an array,
    /// like `[u64; 4]` and not `[[u32; 2]; 4]`.
    pub trait Number: Copy {
        /// Count number of ones.
        fn count_ones(self) -> u32;

        /// Count number of zeros.
        fn count_zeros(self) -> u32;

        /// Set reverse bit.
        fn set_bit_rev<S>(&mut self, index: u32)
        where
            S: Shift;

        /// Clear reverse bit.
        fn clear_bit_rev<S>(&mut self, index: u32)
        where
            S: Shift;

        /// Generate an overflowing mask for the given index.
        fn mask(index: u32) -> Self;

        /// Generate a reverse overflowing mask at the given index, that is at
        /// the `BITS - index - 1` bit location.
        fn mask_rev(index: u32) -> Self;

        /// Count the number of "leading" ones.
        fn ones(self) -> u32;

        /// Count the number of "trailing" ones.
        fn ones_rev(self) -> u32;

        /// Count the number of "leading" zeros.
        fn zeros(self) -> u32;

        /// Count the number of "trailing" zeros.
        fn zeros_rev(self) -> u32;
    }
}

pub(crate) use self::sealed::Number;

macro_rules! number {
    ($ty:ty) => {
        impl Number for $ty {
            #[inline]
            fn count_ones(self) -> u32 {
                <Self>::count_ones(self)
            }

            #[inline]
            fn count_zeros(self) -> u32 {
                <Self>::count_zeros(self)
            }

            #[inline]
            fn set_bit_rev<S>(&mut self, index: u32)
            where
                S: Shift,
            {
                *self |= S::mask_rev::<Self>(index);
            }

            #[inline]
            fn clear_bit_rev<S>(&mut self, index: u32)
            where
                S: Shift,
            {
                *self &= !S::mask_rev::<Self>(index);
            }

            #[inline]
            fn mask(index: u32) -> Self {
                const ONE: $ty = 1 as $ty;
                ONE.wrapping_shl(index)
            }

            #[inline]
            fn mask_rev(index: u32) -> Self {
                const ONE: $ty = !(<$ty>::MAX >> 1);
                ONE.wrapping_shr(index)
            }

            #[inline]
            fn ones(self) -> u32 {
                <$ty>::trailing_ones(self)
            }

            #[inline]
            fn ones_rev(self) -> u32 {
                <$ty>::leading_ones(self)
            }

            #[inline]
            fn zeros(self) -> u32 {
                <$ty>::trailing_zeros(self)
            }

            #[inline]
            fn zeros_rev(self) -> u32 {
                <$ty>::leading_zeros(self)
            }
        }

        impl crate::bits::Sealed for $ty {}

        impl Bits for $ty {
            type IterOnes<'a> = IterOnes<Self, DefaultShift> where Self: 'a;
            type IterOnesWith<'a, S> = IterOnes<Self, S> where Self: 'a, S: Shift;
            type IterZeros<'a> = IterZeros<Self, DefaultShift> where Self: 'a;
            type IterZerosWith<'a, S> = IterZeros<Self, S> where Self: 'a, S: Shift;

            #[inline]
            fn count_ones(&self) -> u32 {
                <$ty>::count_ones(*self)
            }

            #[inline]
            fn count_zeros(&self) -> u32 {
                <$ty>::count_zeros(*self)
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
            fn test_bit_with<S>(&self, index: u32) -> bool
            where
                S: Shift,
            {
                *self & S::mask::<Self>(index) != 0
            }

            #[inline]
            fn iter_ones(&self) -> Self::IterOnes<'_> {
                IterOnes::new(*self)
            }

            #[inline]
            fn iter_ones_with<S>(&self) -> Self::IterOnesWith<'_, S>
            where
                S: Shift,
            {
                IterOnes::new(*self)
            }

            #[inline]
            fn iter_zeros(&self) -> Self::IterZeros<'_> {
                IterZeros::new(*self)
            }

            #[inline]
            fn iter_zeros_with<S>(&self) -> Self::IterZerosWith<'_, S>
            where
                S: Shift,
            {
                IterZeros::new(*self)
            }
        }

        impl BitsMut for $ty {
            #[inline]
            fn set_bit_with<S>(&mut self, index: u32)
            where
                S: Shift,
            {
                *self |= S::mask::<Self>(index);
            }

            #[inline]
            fn clear_bit_with<S>(&mut self, index: u32)
            where
                S: Shift,
            {
                *self &= !S::mask::<Self>(index);
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
                *self &= !other;
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

            type IntoIterOnes = IterOnes<Self, DefaultShift>;
            type IntoIterOnesWith<S> = IterOnes<Self, S> where S: Shift;
            type IntoIterZeros = IterZeros<Self, DefaultShift>;
            type IntoIterZerosWith<S> = IterZeros<Self, S> where S: Shift;

            #[inline]
            fn zeros() -> Self {
                Self::ZEROS
            }

            #[inline]
            fn ones() -> Self {
                Self::ONES
            }

            #[inline]
            fn with_bit_with<S>(self, bit: u32) -> Self
            where
                S: Shift,
            {
                self | S::mask::<Self>(bit)
            }

            #[inline]
            fn without_bit_with<S>(self, bit: u32) -> Self
            where
                S: Shift,
            {
                self & !S::mask::<Self>(bit)
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
                self & !other
            }

            #[inline]
            fn symmetric_difference(self, other: Self) -> Self {
                self ^ other
            }

            #[inline]
            fn into_iter_ones(self) -> Self::IntoIterOnes {
                IterOnes::new(self)
            }

            #[inline]
            fn into_iter_ones_with<S>(self) -> Self::IntoIterOnesWith<S>
            where
                S: Shift,
            {
                IterOnes::new(self)
            }

            #[inline]
            fn into_iter_zeros(self) -> Self::IntoIterZeros {
                IterZeros::new(self)
            }

            #[inline]
            fn into_iter_zeros_with<S>(self) -> Self::IntoIterZerosWith<S>
            where
                S: Shift,
            {
                IterZeros::new(self)
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
pub struct IterOnes<T, S> {
    bits: T,
    shift: PhantomData<S>,
}

impl<T, S> IterOnes<T, S> {
    #[inline]
    const fn new(bits: T) -> Self {
        Self {
            bits,
            shift: PhantomData,
        }
    }
}

impl<T, S> Iterator for IterOnes<T, S>
where
    T: BitsOwned + Number,
    S: Shift,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.all_zeros() {
            return None;
        }

        let index = S::zeros(self.bits);
        self.bits.clear_bit_with::<S>(index);
        Some(index)
    }
}

/// Double ended iterator over ones.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
/// let n: u8 = bittle::set![0, 4];
/// assert!(n.iter_ones().rev().eq([4, 0]));
/// ```
impl<T, S> DoubleEndedIterator for IterOnes<T, S>
where
    T: BitsOwned + Number,
    S: Shift,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits.all_zeros() {
            return None;
        }

        let index = S::zeros_rev(self.bits);
        self.bits.clear_bit_rev::<S>(index);
        Some(T::BITS - index - 1)
    }
}

impl<T, S> ExactSizeIterator for IterOnes<T, S>
where
    T: BitsOwned + Number,
    S: Shift,
{
    #[inline]
    fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }
}

/// An iterator over zeros in a primitive number.
#[derive(Clone)]
#[repr(transparent)]
pub struct IterZeros<T, S> {
    bits: T,
    shift: PhantomData<S>,
}

impl<T, S> IterZeros<T, S> {
    #[inline]
    const fn new(bits: T) -> Self {
        Self {
            bits,
            shift: PhantomData,
        }
    }
}

impl<T, S> Iterator for IterZeros<T, S>
where
    T: BitsMut + Number,
    S: Shift,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.all_ones() {
            return None;
        }

        let index = S::ones(self.bits);
        self.bits.set_bit_with::<S>(index);
        Some(index)
    }
}

impl<T, S> ExactSizeIterator for IterZeros<T, S>
where
    T: BitsMut + Number,
    S: Shift,
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
/// let n: u8 = bittle::set![0, 4];
/// assert!(n.iter_zeros().rev().eq([7, 6, 5, 3, 2, 1]));
/// ```
impl<T, S> DoubleEndedIterator for IterZeros<T, S>
where
    T: BitsOwned + Number,
    S: Shift,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits.all_ones() {
            return None;
        }

        let index = S::ones_rev(self.bits);
        self.bits.set_bit_rev::<S>(index);
        Some(T::BITS - index - 1)
    }
}
