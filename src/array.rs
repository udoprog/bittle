//! [Bits] associated types for primitive arrays.

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::shift::{DefaultShift, Shift};
use crate::slice::{IterOnes, IterZeros};

impl<T, const N: usize> BitsOwned for [T; N]
where
    T: Copy + Eq + BitsOwned,
{
    #[allow(clippy::cast_possible_truncation)]
    const BITS: u32 = match T::BITS.checked_mul(N as u32) {
        Some(value) => value,
        None => panic!("32-bit overflow in capacity"),
    };
    const ZEROS: Self = [T::ZEROS; N];
    const ONES: Self = [T::ONES; N];

    type IntoIterOnes = IntoIterOnes<T, N, DefaultShift>;
    type IntoIterOnesWith<S> = IntoIterOnes<T, N, S> where S: Shift;
    type IntoIterZeros = IntoIterZeros<T, N, DefaultShift>;
    type IntoIterZerosWith<S> = IntoIterZeros<T, N, S> where S: Shift;

    #[inline]
    fn zeros() -> Self {
        Self::ZEROS
    }

    #[inline]
    fn ones() -> Self {
        Self::ONES
    }

    #[inline]
    fn with_bit_with<S>(mut self, bit: u32) -> Self
    where
        S: Shift,
    {
        self[(bit / T::BITS) as usize % N].set_bit_with::<S>(bit % T::BITS);
        self
    }

    #[inline]
    fn without_bit_with<S>(mut self, bit: u32) -> Self
    where
        S: Shift,
    {
        self[(bit / T::BITS) as usize % N].clear_bit_with::<S>(bit % T::BITS);
        self
    }

    #[inline]
    fn union(mut self, other: Self) -> Self {
        for (o, i) in self.iter_mut().zip(other) {
            o.union_assign(&i);
        }

        self
    }

    #[inline]
    fn conjunction(mut self, other: Self) -> Self {
        for (o, i) in self.iter_mut().zip(other) {
            o.conjunction_assign(&i);
        }

        self
    }

    #[inline]
    fn difference(mut self, other: Self) -> Self {
        for (o, i) in self.iter_mut().zip(other) {
            o.difference_assign(&i);
        }

        self
    }

    #[inline]
    fn symmetric_difference(mut self, other: Self) -> Self {
        for (o, i) in self.iter_mut().zip(other) {
            o.symmetric_difference_assign(&i);
        }

        self
    }

    #[inline]
    fn into_iter_ones(self) -> Self::IntoIterOnes {
        IntoIterOnes::new(self)
    }

    #[inline]
    fn into_iter_ones_with<S>(self) -> Self::IntoIterOnesWith<S>
    where
        S: Shift,
    {
        IntoIterOnes::new(self)
    }

    #[inline]
    fn into_iter_zeros(self) -> Self::IntoIterZeros {
        IntoIterZeros::new(self)
    }

    #[inline]
    fn into_iter_zeros_with<S>(self) -> Self::IntoIterZerosWith<S>
    where
        S: Shift,
    {
        IntoIterZeros::new(self)
    }
}

impl<T, const N: usize> Bits for [T; N]
where
    T: Copy + Eq + BitsOwned,
{
    type IterOnes<'a> = IterOnes<'a, T, DefaultShift> where Self: 'a;
    type IterOnesWith<'a, S> = IterOnes<'a, T, S> where Self: 'a, S: Shift;
    type IterZeros<'a> = IterZeros<'a, T, DefaultShift> where Self: 'a;
    type IterZerosWith<'a, S> = IterZeros<'a, T, S> where Self: 'a, S: Shift;

    #[inline]
    fn count_ones(&self) -> u32 {
        self.iter().map(Bits::count_ones).sum()
    }

    #[inline]
    fn count_zeros(&self) -> u32 {
        self.iter().map(Bits::count_zeros).sum()
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
        self[(index / T::BITS) as usize % N].test_bit_with::<S>(index % T::BITS)
    }

    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        IterOnes::new(self)
    }

    #[inline]
    fn iter_ones_with<S>(&self) -> Self::IterOnesWith<'_, S>
    where
        S: Shift,
    {
        IterOnes::new(self)
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        IterZeros::new(self)
    }

    #[inline]
    fn iter_zeros_with<S>(&self) -> Self::IterZerosWith<'_, S>
    where
        S: Shift,
    {
        IterZeros::new(self)
    }
}

impl<T, const N: usize> BitsMut for [T; N]
where
    T: Copy + Eq + BitsOwned,
{
    #[inline]
    fn set_bit_with<S>(&mut self, index: u32)
    where
        S: Shift,
    {
        self[(index / T::BITS) as usize % N].set_bit_with::<S>(index % T::BITS);
    }

    #[inline]
    fn clear_bit_with<S>(&mut self, index: u32)
    where
        S: Shift,
    {
        self[(index / T::BITS) as usize % N].clear_bit_with::<S>(index % T::BITS);
    }

    #[inline]
    fn clear_bits(&mut self) {
        for b in self {
            b.clear_bits();
        }
    }

    #[inline]
    fn union_assign(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.union_assign(i);
        }
    }

    #[inline]
    fn conjunction_assign(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.conjunction_assign(i);
        }
    }

    #[inline]
    fn difference_assign(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.difference_assign(i);
        }
    }

    #[inline]
    fn symmetric_difference_assign(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.symmetric_difference_assign(i);
        }
    }
}

/// An owned iterator over the bits set to one in an array.
#[derive(Clone)]
pub struct IntoIterOnes<T, const N: usize, S>
where
    T: BitsOwned,
    S: Shift,
{
    iter: core::array::IntoIter<T, N>,
    current: Option<(T::IntoIterOnesWith<S>, u32)>,
}

impl<T, const N: usize, S> IntoIterOnes<T, N, S>
where
    T: BitsOwned,
    S: Shift,
{
    #[inline]
    fn new(array: [T; N]) -> Self {
        let mut iter = array.into_iter();
        let current = iter.next().map(|v| (v.into_iter_ones_with(), 0));
        Self { iter, current }
    }
}

impl<T, const N: usize, S> Iterator for IntoIterOnes<T, N, S>
where
    T: BitsOwned,
    S: Shift,
{
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (it, offset) = self.current.as_mut()?;

            if let Some(index) = it.next() {
                return offset.checked_add(index);
            }

            self.current = Some((
                self.iter.next()?.into_iter_ones_with(),
                offset.checked_add(T::BITS)?,
            ));
        }
    }
}

/// An owned iterator over the bits set to zero in an array.
#[derive(Clone)]
pub struct IntoIterZeros<T, const N: usize, S>
where
    T: BitsOwned,
    S: Shift,
{
    iter: core::array::IntoIter<T, N>,
    current: Option<(T::IntoIterZerosWith<S>, u32)>,
}

impl<T, const N: usize, S> IntoIterZeros<T, N, S>
where
    T: BitsOwned,
    S: Shift,
{
    #[inline]
    fn new(array: [T; N]) -> Self {
        let mut iter = array.into_iter();
        let current = iter.next().map(|v| (v.into_iter_zeros_with(), 0));
        Self { iter, current }
    }
}

impl<T, const N: usize, S> Iterator for IntoIterZeros<T, N, S>
where
    T: BitsOwned,
    S: Shift,
{
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (it, offset) = self.current.as_mut()?;

            if let Some(index) = it.next() {
                return offset.checked_add(index);
            }

            self.current = Some((
                self.iter.next()?.into_iter_zeros_with(),
                offset.checked_add(T::BITS)?,
            ));
        }
    }
}
