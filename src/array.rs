//! [Bits] implementation and associated types for arrays.

use crate::bits::{Bits, OwnedBits};
use crate::number::Number;
use crate::slice::IterOnes;

impl<T, const N: usize> OwnedBits for [T; N]
where
    T: Eq + OwnedBits + Number,
{
    const BITS: u32 = T::BITS * N as u32;
    const ZEROS: Self = [T::ZEROS; N];
    const ONES: Self = [T::ONES; N];

    type IntoIterOnes = IntoIterOnes<T, N>;

    #[inline]
    fn zeros() -> Self {
        Self::ZEROS
    }

    #[inline]
    fn ones() -> Self {
        Self::ONES
    }

    #[inline]
    fn with(mut self, bit: u32) -> Self {
        if let Some(bits) = self.get_mut(((bit / T::BITS) % (N as u32)) as usize) {
            bits.bit_set(bit % T::BITS);
        }

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
        let mut iter = IntoIterator::into_iter(self);
        let current = iter.next().map(|v| (v, 0));
        IntoIterOnes { iter, current }
    }
}

impl<T, const N: usize> Bits for [T; N]
where
    T: Eq + OwnedBits + Number,
{
    type IterOnes<'a> = IterOnes<'a, T> where Self: 'a;

    #[inline]
    fn bits_len(&self) -> u32 {
        self.iter().map(Bits::bits_len).sum()
    }

    #[inline]
    fn bits_capacity(&self) -> u32 {
        T::BITS.saturating_mul(N as u32)
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
        if let Some(bits) = self.get((index / T::BITS) as usize) {
            return bits.bit_test(index % T::BITS);
        }

        false
    }

    #[inline]
    fn bit_set(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.bit_set(index % T::BITS);
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

    #[inline]
    fn bit_clear(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.bit_clear(index % T::BITS);
        }
    }

    #[inline]
    fn bits_clear(&mut self) {
        for b in self {
            b.bits_clear();
        }
    }

    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        IterOnes::new(IntoIterator::into_iter(self))
    }
}

/// An iterator over the bits of an array acting as a bit set.
#[derive(Clone)]
pub struct IntoIterOnes<T, const N: usize> {
    iter: core::array::IntoIter<T, N>,
    current: Option<(T, u32)>,
}

impl<T, const N: usize> Iterator for IntoIterOnes<T, N>
where
    T: OwnedBits + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some((bits, offset)) = &mut self.current else {
                return None;
            };

            if !bits.is_zeros() {
                let index = T::trailing_zeros(*bits);
                bits.bit_clear(index);
                return Some(*offset + index);
            }

            self.current = Some((self.iter.next()?, *offset + T::BITS));
        }
    }
}
