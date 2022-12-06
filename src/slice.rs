//! [Bits] implementation and associated types for slices.

use crate::bits::Bits;
use crate::number::Number;
use crate::OwnedBits;

impl<T> Bits for [T]
where
    T: OwnedBits + Number,
{
    type IterOnes<'a> = IterOnes<'a, T> where Self: 'a;

    #[inline]
    fn bits_len(&self) -> u32 {
        self.iter().map(|b| b.bits_len()).sum()
    }

    #[inline]
    fn bits_capacity(&self) -> u32 {
        Bits::bits_len(self).saturating_mul(T::BITS)
    }

    #[inline]
    fn is_zeros(&self) -> bool {
        self.iter().all(|b| b.is_zeros())
    }

    #[inline]
    fn is_ones(&self) -> bool {
        self.iter().all(|b| b.is_ones())
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

/// A borrowing iterator over the bits set to ones in a slice.
#[derive(Clone)]
pub struct IterOnes<'a, T> {
    iter: core::slice::Iter<'a, T>,
    current: Option<(T, u32)>,
}

impl<'a, T> IterOnes<'a, T>
where
    T: Copy,
{
    pub(crate) fn new(mut iter: core::slice::Iter<'a, T>) -> Self {
        let current = iter.next().map(|v| (*v, 0));
        Self { iter, current }
    }
}

impl<'a, T> Iterator for IterOnes<'a, T>
where
    T: OwnedBits + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (bits, offset) = self.current.as_mut()?;

            if !bits.is_zeros() {
                let index = bits.trailing_zeros();
                bits.bit_clear(index);
                return Some(*offset + index);
            }

            self.current = Some((*self.iter.next()?, *offset + T::BITS));
        }
    }
}
