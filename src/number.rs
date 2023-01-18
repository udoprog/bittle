//! [Bits] associated types for primitive numbers.

use core::iter::FusedIterator;
use core::marker::PhantomData;

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::endian::{DefaultEndian, Endian};

mod sealed {
    use core::ops::{BitAndAssign, BitOrAssign, Not};

    /// Basic numerical trait for the plumbing of a bit set. This ensures that only
    /// primitive types can be used as the basis of a bit set backed by an array,
    /// like `[u64; 4]` and not `[[u32; 2]; 4]`.
    pub trait Number: Copy + Not<Output = Self> + BitAndAssign + BitOrAssign + Eq {
        const ZEROS: Self;
        const ONES: Self;
        const BITS: u32;
        const BIT_RIGHT: Self;
        const BIT_LEFT: Self;

        fn count_ones(self) -> u32;
        fn count_zeros(self) -> u32;
        fn trailing_ones(self) -> u32;
        fn leading_ones(self) -> u32;
        fn trailing_zeros(self) -> u32;
        fn leading_zeros(self) -> u32;
        fn wrapping_shl(self, index: u32) -> Self;
        fn wrapping_shr(self, index: u32) -> Self;
    }
}

pub(crate) use self::sealed::Number;

macro_rules! number {
    ($ty:ty) => {
        impl Number for $ty {
            const ONES: $ty = !0;
            const ZEROS: $ty = 0;
            const BITS: u32 = (core::mem::size_of::<$ty>() * 8) as u32;
            const BIT_RIGHT: $ty = 1 as $ty;
            const BIT_LEFT: $ty = !(<$ty>::MAX >> 1);

            #[inline]
            fn count_ones(self) -> u32 {
                <$ty>::count_ones(self)
            }

            #[inline]
            fn count_zeros(self) -> u32 {
                <$ty>::count_zeros(self)
            }

            #[inline]
            fn trailing_ones(self) -> u32 {
                <$ty>::trailing_ones(self)
            }

            #[inline]
            fn leading_ones(self) -> u32 {
                <$ty>::leading_ones(self)
            }

            #[inline]
            fn trailing_zeros(self) -> u32 {
                <$ty>::trailing_zeros(self)
            }

            #[inline]
            fn leading_zeros(self) -> u32 {
                <$ty>::leading_zeros(self)
            }

            #[inline]
            fn wrapping_shl(self, index: u32) -> Self {
                <$ty>::wrapping_shl(self, index)
            }

            #[inline]
            fn wrapping_shr(self, index: u32) -> Self {
                <$ty>::wrapping_shr(self, index)
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
                <Self as Number>::BITS
            }

            #[inline]
            fn all_zeros(&self) -> bool {
                <$ty as Number>::ZEROS == *self
            }

            #[inline]
            fn all_ones(&self) -> bool {
                <$ty as Number>::ONES == *self
            }

            #[inline]
            fn test_bit(&self, index: u32) -> bool {
                self.test_bit_in::<DefaultEndian>(index)
            }

            #[inline]
            fn test_bit_in<E>(&self, index: u32) -> bool
            where
                E: Endian,
            {
                *self & E::mask::<Self>(index) != 0
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
                *self = <$ty as Number>::ZEROS;
            }
        }

        impl BitsOwned for $ty {
            const BITS: u32 = <$ty as Number>::BITS;
            const ZEROS: Self = <$ty as Number>::ZEROS;
            const ONES: Self = <$ty as Number>::ONES;

            type IntoIterOnes = IterOnes<Self, DefaultEndian>;
            type IntoIterOnesIn<E> = IterOnes<Self, E> where E: Endian;
            type IntoIterZeros = IterZeros<Self, DefaultEndian>;
            type IntoIterZerosIn<E> = IterZeros<Self, E> where E: Endian;

            #[inline]
            fn zeros() -> Self {
                <$ty as Number>::ZEROS
            }

            #[inline]
            fn ones() -> Self {
                <$ty as Number>::ONES
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

/// Iterator over ones.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let n: u8 = bittle::set![0, 4];
/// assert!(n.iter_ones().eq([0, 4]));
/// ```
impl<T, E> Iterator for IterOnes<T, E>
where
    T: Number,
    E: Endian,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits == T::ZEROS {
            return None;
        }

        let index = E::zeros(self.bits);
        self.bits &= !E::mask::<T>(index);
        Some(index)
    }
}

/// Double ended iterator over ones.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let n: u8 = bittle::set![0, 4];
/// assert!(n.iter_ones().rev().eq([4, 0]));
/// ```
impl<T, E> DoubleEndedIterator for IterOnes<T, E>
where
    T: Number,
    E: Endian,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits == T::ZEROS {
            return None;
        }

        let index = E::zeros_rev(self.bits);
        self.bits &= !E::mask_rev::<T>(index);
        Some(T::BITS - index - 1)
    }
}

/// Exact size iterator over ones.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let n: u8 = bittle::set![0, 4];
/// assert_eq!(n.iter_ones().len(), 2);
/// ```
impl<T, E> ExactSizeIterator for IterOnes<T, E>
where
    T: Number,
    E: Endian,
{
    #[inline]
    fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }
}

impl<T, E> FusedIterator for IterOnes<T, E>
where
    T: Number,
    E: Endian,
{
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

/// Iterator over zeros.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let n: u8 = bittle::set![0, 4, 6];
/// assert!(n.iter_zeros().eq([1, 2, 3, 5, 7]));
/// ```
impl<T, E> Iterator for IterZeros<T, E>
where
    T: Number,
    E: Endian,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits == T::ONES {
            return None;
        }

        let index = E::ones(self.bits);
        self.bits |= E::mask::<T>(index);
        Some(index)
    }
}

/// Exact size iterator over zeros.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let n: u8 = bittle::set![0, 4];
/// assert_eq!(n.iter_zeros().len(), 6);
/// ```
impl<T, E> ExactSizeIterator for IterZeros<T, E>
where
    T: Number,
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
///
/// let n: u8 = bittle::set![0, 4, 6];
/// assert!(n.iter_zeros().rev().eq([7, 5, 3, 2, 1]));
/// ```
impl<T, E> DoubleEndedIterator for IterZeros<T, E>
where
    T: Number,
    E: Endian,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bits == T::ONES {
            return None;
        }

        let index = E::ones_rev(self.bits);
        self.bits |= E::mask_rev::<T>(index);
        Some(T::BITS - index - 1)
    }
}

impl<T, E> FusedIterator for IterZeros<T, E>
where
    T: Number,
    E: Endian,
{
}
