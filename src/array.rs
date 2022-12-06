//! [Bits] implementation and associated types for arrays.

use crate::bits::{Bits, OwnedBits};
use crate::number::Number;
use crate::slice::BitsIter;

impl<T, const N: usize> OwnedBits for [T; N]
where
    T: Number,
{
    const BITS: u32 = T::NUMBER_BITS * N as u32;
    const EMPTY: Self = [T::EMPTY; N];
    const FULL: Self = [T::FULL; N];

    type IntoBitsIter = IntoBitsIter<T, N>;

    #[inline]
    fn empty() -> Self {
        Self::EMPTY
    }

    #[inline]
    fn full() -> Self {
        Self::FULL
    }

    #[inline]
    fn into_bits(self) -> Self::IntoBitsIter {
        let mut iter = IntoIterator::into_iter(self);
        let current = iter.next().map(|v| (v, 0));
        IntoBitsIter { iter, current }
    }
}

impl<T, const N: usize> Bits for [T; N]
where
    T: Number,
{
    type BitsIter<'a> = BitsIter<'a, T> where Self: 'a;

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
        if let Some(bits) = self.get((index / T::NUMBER_BITS) as usize) {
            return bits.test(index % T::NUMBER_BITS);
        }

        false
    }

    #[inline]
    fn set(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::NUMBER_BITS) as usize) {
            bits.set(index % T::NUMBER_BITS);
        }
    }

    #[inline]
    fn union(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.union(i);
        }
    }

    #[inline]
    fn difference(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.difference(i);
        }
    }

    #[inline]
    fn symmetric_difference(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.symmetric_difference(i);
        }
    }

    #[inline]
    fn unset(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::NUMBER_BITS) as usize) {
            bits.unset(index % T::NUMBER_BITS);
        }
    }

    #[inline]
    fn clear(&mut self) {
        for b in self {
            b.clear();
        }
    }

    #[inline]
    fn bits(&self) -> Self::BitsIter<'_> {
        BitsIter::new(IntoIterator::into_iter(self))
    }
}

/// An iterator over the bits of an array acting as a bit set.
#[derive(Clone)]
pub struct IntoBitsIter<T, const N: usize>
where
    T: Number,
{
    iter: core::array::IntoIter<T, N>,
    current: Option<(T, u32)>,
}

impl<T, const N: usize> Iterator for IntoBitsIter<T, N>
where
    T: Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some((bits, offset)) = &mut self.current else {
                return None;
            };

            if !bits.is_empty() {
                let index = bits.trailing_zeros();
                bits.unset(index);
                return Some(*offset + index);
            }

            self.current = Some((self.iter.next()?, *offset + T::NUMBER_BITS));
        }
    }
}
