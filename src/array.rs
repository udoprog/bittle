//! [Bits] implementation and associated types for arrays.

use crate::bits::{Bits, OwnedBits};
use crate::number::Number;
use crate::slice::IterBits;

impl<T, const N: usize> OwnedBits for [T; N]
where
    T: Eq + OwnedBits + Number,
{
    const BITS: u32 = T::BITS * N as u32;
    const EMPTY: Self = [T::EMPTY; N];
    const FULL: Self = [T::FULL; N];

    type IntoBits = IntoBits<T, N>;

    #[inline]
    fn empty() -> Self {
        Self::EMPTY
    }

    #[inline]
    fn full() -> Self {
        Self::FULL
    }

    #[inline]
    fn with(mut self, bit: u32) -> Self {
        if let Some(bits) = self.get_mut(((bit / T::BITS) % (N as u32)) as usize) {
            bits.set(bit % T::BITS);
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
    fn into_bits(self) -> Self::IntoBits {
        let mut iter = IntoIterator::into_iter(self);
        let current = iter.next().map(|v| (v, 0));
        IntoBits { iter, current }
    }
}

impl<T, const N: usize> Bits for [T; N]
where
    T: Eq + OwnedBits + Number,
{
    type IterBits<'a> = IterBits<'a, T> where Self: 'a;

    #[inline]
    fn len(&self) -> u32 {
        self.iter().map(Bits::len).sum()
    }

    #[inline]
    fn capacity(&self) -> u32 {
        T::BITS.saturating_mul(N as u32)
    }

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
        if let Some(bits) = self.get((index / T::BITS) as usize) {
            return bits.test(index % T::BITS);
        }

        false
    }

    #[inline]
    fn set(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.set(index % T::BITS);
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
    fn unset(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.unset(index % T::BITS);
        }
    }

    #[inline]
    fn clear(&mut self) {
        for b in self {
            b.clear();
        }
    }

    #[inline]
    fn iter_bits(&self) -> Self::IterBits<'_> {
        IterBits::new(IntoIterator::into_iter(self))
    }
}

/// An iterator over the bits of an array acting as a bit set.
#[derive(Clone)]
pub struct IntoBits<T, const N: usize> {
    iter: core::array::IntoIter<T, N>,
    current: Option<(T, u32)>,
}

impl<T, const N: usize> Iterator for IntoBits<T, N>
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

            if !bits.is_empty() {
                let index = T::trailing_zeros(*bits);
                bits.unset(index);
                return Some(*offset + index);
            }

            self.current = Some((self.iter.next()?, *offset + T::BITS));
        }
    }
}
