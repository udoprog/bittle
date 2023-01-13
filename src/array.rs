//! [Bits] associated types for primitive arrays.

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::endian::{DefaultEndian, Endian};
use crate::slice::{IterOnes, IterZeros};

impl<T, const N: usize> BitsOwned for [T; N]
where
    T: Eq + BitsOwned,
{
    #[allow(clippy::cast_possible_truncation)]
    const BITS: u32 = match T::BITS.checked_mul(N as u32) {
        Some(value) => value,
        None => panic!("32-bit overflow in capacity"),
    };
    const ZEROS: Self = [T::ZEROS; N];
    const ONES: Self = [T::ONES; N];

    type IntoIterOnes = IntoIterOnes<T, N, DefaultEndian>;
    type IntoIterOnesIn<E> = IntoIterOnes<T, N, E> where E: Endian;
    type IntoIterZeros = IntoIterZeros<T, N, DefaultEndian>;
    type IntoIterZerosIn<E> = IntoIterZeros<T, N, E> where E: Endian;

    #[inline]
    fn zeros() -> Self {
        Self::ZEROS
    }

    #[inline]
    fn ones() -> Self {
        Self::ONES
    }

    #[inline]
    fn with_bit_in<E>(mut self, bit: u32) -> Self
    where
        E: Endian,
    {
        self[(bit / T::BITS) as usize % N].set_bit_in::<E>(bit % T::BITS);
        self
    }

    #[inline]
    fn with_bit(self, bit: u32) -> Self {
        self.with_bit_in::<DefaultEndian>(bit)
    }

    #[inline]
    fn without_bit_in<E>(mut self, bit: u32) -> Self
    where
        E: Endian,
    {
        self[(bit / T::BITS) as usize % N].clear_bit_in::<E>(bit % T::BITS);
        self
    }

    #[inline]
    fn without_bit(self, bit: u32) -> Self {
        self.without_bit_in::<DefaultEndian>(bit)
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
    fn into_iter_ones_in<E>(self) -> Self::IntoIterOnesIn<E>
    where
        E: Endian,
    {
        IntoIterOnes::new(self)
    }

    #[inline]
    fn into_iter_zeros(self) -> Self::IntoIterZeros {
        IntoIterZeros::new(self)
    }

    #[inline]
    fn into_iter_zeros_in<E>(self) -> Self::IntoIterZerosIn<E>
    where
        E: Endian,
    {
        IntoIterZeros::new(self)
    }
}

impl<T, const N: usize> Bits for [T; N]
where
    T: Eq + BitsOwned,
{
    type IterOnes<'a> = IterOnes<'a, T, DefaultEndian> where Self: 'a;
    type IterOnesIn<'a, E> = IterOnes<'a, T, E> where Self: 'a, E: Endian;
    type IterZeros<'a> = IterZeros<'a, T, DefaultEndian> where Self: 'a;
    type IterZerosIn<'a, E> = IterZeros<'a, T, E> where Self: 'a, E: Endian;

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
    fn test_bit_in<E>(&self, index: u32) -> bool
    where
        E: Endian,
    {
        self[(index / T::BITS) as usize % N].test_bit_in::<E>(index % T::BITS)
    }

    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        self.test_bit_in::<DefaultEndian>(index)
    }

    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        IterOnes::new(self)
    }

    #[inline]
    fn iter_ones_in<E>(&self) -> Self::IterOnesIn<'_, E>
    where
        E: Endian,
    {
        IterOnes::new(self)
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        IterZeros::new(self)
    }

    #[inline]
    fn iter_zeros_in<E>(&self) -> Self::IterZerosIn<'_, E>
    where
        E: Endian,
    {
        IterZeros::new(self)
    }
}

impl<T, const N: usize> BitsMut for [T; N]
where
    T: Eq + BitsOwned,
{
    #[inline]
    fn set_bit_in<E>(&mut self, index: u32)
    where
        E: Endian,
    {
        self[(index / T::BITS) as usize % N].set_bit_in::<E>(index % T::BITS);
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
        self[(index / T::BITS) as usize % N].clear_bit_in::<E>(index % T::BITS);
    }

    #[inline]
    fn clear_bit(&mut self, index: u32) {
        self.clear_bit_in::<DefaultEndian>(index);
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
pub struct IntoIterOnes<T, const N: usize, E>
where
    T: BitsOwned,
    E: Endian,
{
    iter: core::array::IntoIter<T, N>,
    current: Option<(T::IntoIterOnesIn<E>, u32)>,
}

impl<T, const N: usize, E> Clone for IntoIterOnes<T, N, E>
where
    T: Clone + BitsOwned,
    E: Endian,
    T::IntoIterOnesIn<E>: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            current: self.current.clone(),
        }
    }
}

impl<T, const N: usize, E> IntoIterOnes<T, N, E>
where
    T: BitsOwned,
    E: Endian,
{
    #[inline]
    fn new(array: [T; N]) -> Self {
        let mut iter = array.into_iter();
        let current = iter.next().map(|v| (v.into_iter_ones_in(), 0));
        Self { iter, current }
    }
}

impl<T, const N: usize, E> Iterator for IntoIterOnes<T, N, E>
where
    T: BitsOwned,
    E: Endian,
{
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (it, offset) = self.current.as_mut()?;

            if let Some(index) = it.next() {
                return offset.checked_add(index);
            }

            self.current = Some((
                self.iter.next()?.into_iter_ones_in(),
                offset.checked_add(T::BITS)?,
            ));
        }
    }
}

/// An owned iterator over the bits set to zero in an array.
pub struct IntoIterZeros<T, const N: usize, E>
where
    T: BitsOwned,
    E: Endian,
{
    iter: core::array::IntoIter<T, N>,
    current: Option<(T::IntoIterZerosIn<E>, u32)>,
}

impl<T, const N: usize, E> Clone for IntoIterZeros<T, N, E>
where
    T: Clone + BitsOwned,
    E: Endian,
    T::IntoIterZerosIn<E>: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            current: self.current.clone(),
        }
    }
}

impl<T, const N: usize, E> IntoIterZeros<T, N, E>
where
    T: BitsOwned,
    E: Endian,
{
    #[inline]
    fn new(array: [T; N]) -> Self {
        let mut iter = array.into_iter();
        let current = iter.next().map(|v| (v.into_iter_zeros_in(), 0));
        Self { iter, current }
    }
}

impl<T, const N: usize, E> Iterator for IntoIterZeros<T, N, E>
where
    T: BitsOwned,
    E: Endian,
{
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (it, offset) = self.current.as_mut()?;

            if let Some(index) = it.next() {
                return offset.checked_add(index);
            }

            self.current = Some((
                self.iter.next()?.into_iter_zeros_in(),
                offset.checked_add(T::BITS)?,
            ));
        }
    }
}
