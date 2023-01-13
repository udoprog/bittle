//! [Bits] associated types for primitive numbers.

use core::marker::PhantomData;

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::endian::{DefaultEndian, Endian};

mod sealed {
    use crate::endian::Endian;

    /// Basic numerical trait for the plumbing of a bit set. This ensures that only
    /// primitive types can be used as the basis of a bit set backed by an array,
    /// like `[u64; 4]` and not `[[u32; 2]; 4]`.
    pub trait Number: Copy {
        /// Count number of ones.
        fn count_ones(self) -> u32;

        /// Count number of zeros.
        fn count_zeros(self) -> u32;

        /// Set reverse bit.
        fn set_bit_rev<E>(&mut self, index: u32)
        where
            E: Endian;

        /// Clear reverse bit.
        fn clear_bit_rev<E>(&mut self, index: u32)
        where
            E: Endian;

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
            fn set_bit_rev<E>(&mut self, index: u32)
            where
                E: Endian,
            {
                *self |= E::mask_rev::<Self>(index);
            }

            #[inline]
            fn clear_bit_rev<E>(&mut self, index: u32)
            where
                E: Endian,
            {
                *self &= !E::mask_rev::<Self>(index);
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
            type IterOnes<'a> = IterOnes<Self, DefaultEndian> where Self: 'a;
            type IterOnesIn<'a, E> = IterOnes<Self, E> where Self: 'a, E: Endian;
            type IterZeros<'a> = IterZeros<Self, DefaultEndian> where Self: 'a;
            type IterZerosIn<'a, E> = IterZeros<Self, E> where Self: 'a, E: Endian;

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
            fn test_bit_in<E>(&self, index: u32) -> bool
            where
                E: Endian,
            {
                *self & E::mask::<Self>(index) != 0
            }

            #[inline]
            fn test_bit(&self, index: u32) -> bool {
                self.test_bit_in::<DefaultEndian>(index)
            }

            #[inline]
            fn iter_ones(&self) -> Self::IterOnes<'_> {
                IterOnes::new(*self)
            }

            #[inline]
            fn iter_ones_in<E>(&self) -> Self::IterOnesIn<'_, E>
            where
                E: Endian,
            {
                IterOnes::new(*self)
            }

            #[inline]
            fn iter_zeros(&self) -> Self::IterZeros<'_> {
                IterZeros::new(*self)
            }

            #[inline]
            fn iter_zeros_in<E>(&self) -> Self::IterZerosIn<'_, E>
            where
                E: Endian,
            {
                IterZeros::new(*self)
            }
        }

        impl BitsMut for $ty {
            #[inline]
            fn set_bit_in<E>(&mut self, index: u32)
            where
                E: Endian,
            {
                *self |= E::mask::<Self>(index);
            }

            #[inline]
            fn set_bit(&mut self, index: u32) {
                self.set_bit_in::<DefaultEndian>(index);
            }

            #[inline]
            fn clear_bit_in<E>(&mut self, index: u32)
            where
                E: Endian,
            {
                *self &= !E::mask::<Self>(index);
            }

            #[inline]
            fn clear_bit(&mut self, index: u32) {
                self.clear_bit_in::<DefaultEndian>(index);
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

            type IntoIterOnes = IterOnes<Self, DefaultEndian>;
            type IntoIterOnesIn<E> = IterOnes<Self, E> where E: Endian;
            type IntoIterZeros = IterZeros<Self, DefaultEndian>;
            type IntoIterZerosIn<E> = IterZeros<Self, E> where E: Endian;

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
                self.with_bit_in::<DefaultEndian>(bit)
            }

            #[inline]
            fn with_bit_in<E>(self, bit: u32) -> Self
            where
                E: Endian,
            {
                self | E::mask::<Self>(bit)
            }

            #[inline]
            fn without_bit(self, bit: u32) -> Self {
                self.without_bit_in::<DefaultEndian>(bit)
            }

            #[inline]
            fn without_bit_in<E>(self, bit: u32) -> Self
            where
                E: Endian,
            {
                self & !E::mask::<Self>(bit)
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
            fn into_iter_ones_in<E>(self) -> Self::IntoIterOnesIn<E>
            where
                E: Endian,
            {
                IterOnes::new(self)
            }

            #[inline]
            fn into_iter_zeros(self) -> Self::IntoIterZeros {
                IterZeros::new(self)
            }

            #[inline]
            fn into_iter_zeros_in<E>(self) -> Self::IntoIterZerosIn<E>
            where
                E: Endian,
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
pub struct IterOnes<T, E> {
    bits: T,
    _shift: PhantomData<E>,
}

impl<T, E> IterOnes<T, E> {
    #[inline]
    const fn new(bits: T) -> Self {
        Self {
            bits,
            _shift: PhantomData,
        }
    }
}

impl<T, E> Iterator for IterOnes<T, E>
where
    T: BitsOwned + Number,
    E: Endian,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.all_zeros() {
            return None;
        }

        let index = E::zeros(self.bits);
        self.bits.clear_bit_in::<E>(index);
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
impl<T, E> DoubleEndedIterator for IterOnes<T, E>
where
    T: BitsOwned + Number,
    E: Endian,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits.all_zeros() {
            return None;
        }

        let index = E::zeros_rev(self.bits);
        self.bits.clear_bit_rev::<E>(index);
        Some(T::BITS - index - 1)
    }
}

impl<T, E> ExactSizeIterator for IterOnes<T, E>
where
    T: BitsOwned + Number,
    E: Endian,
{
    #[inline]
    fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }
}

/// An iterator over zeros in a primitive number.
#[derive(Clone)]
#[repr(transparent)]
pub struct IterZeros<T, E> {
    bits: T,
    _shift: PhantomData<E>,
}

impl<T, E> IterZeros<T, E> {
    #[inline]
    const fn new(bits: T) -> Self {
        Self {
            bits,
            _shift: PhantomData,
        }
    }
}

impl<T, E> Iterator for IterZeros<T, E>
where
    T: BitsMut + Number,
    E: Endian,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits.all_ones() {
            return None;
        }

        let index = E::ones(self.bits);
        self.bits.set_bit_in::<E>(index);
        Some(index)
    }
}

impl<T, E> ExactSizeIterator for IterZeros<T, E>
where
    T: BitsMut + Number,
    E: Endian,
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
impl<T, E> DoubleEndedIterator for IterZeros<T, E>
where
    T: BitsOwned + Number,
    E: Endian,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits.all_ones() {
            return None;
        }

        let index = E::ones_rev(self.bits);
        self.bits.set_bit_rev::<E>(index);
        Some(T::BITS - index - 1)
    }
}
