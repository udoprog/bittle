//! [Bits] implementation and associated types for slices.

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::number::Number;
use crate::BitsOwned;

impl<T> Bits for [T]
where
    T: BitsOwned + Number,
{
    type IterOnes<'a> = IterOnes<'a, T> where Self: 'a;
    type IterZeros<'a> = IterZeros<'a, T> where Self: 'a;

    #[inline]
    fn count_ones(&self) -> u32 {
        self.iter().map(Bits::count_ones).sum()
    }

    #[inline]
    fn bits_capacity(&self) -> u32 {
        Bits::count_ones(self).saturating_mul(T::BITS)
    }

    #[inline]
    fn is_zeros(&self) -> bool {
        self.iter().all(Bits::is_zeros)
    }

    #[inline]
    fn is_ones(&self) -> bool {
        self.iter().all(Bits::is_ones)
    }

    #[inline]
    fn bit_test(&self, index: u32) -> bool {
        self[((index / T::BITS) as usize % self.len())].bit_test(index % T::BITS)
    }

    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        IterOnes::new(IntoIterator::into_iter(self))
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        IterZeros::new(IntoIterator::into_iter(self))
    }
}

impl<T> BitsMut for [T]
where
    T: BitsOwned + Number,
{
    #[inline]
    fn bit_set(&mut self, index: u32) {
        self[((index / T::BITS) as usize % self.len())].bit_set(index % T::BITS);
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
}

/// A borrowing iterator over the bits set to one in a slice.
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
    T: BitsOwned + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (bits, offset) = self.current.as_mut()?;

            if !bits.is_zeros() {
                let index = bits.leading_zeros();
                bits.bit_clear(index);
                return Some(*offset + index);
            }

            self.current = Some((*self.iter.next()?, *offset + T::BITS));
        }
    }
}

/// A borrowing iterator over the bits set to one in a slice.
#[derive(Clone)]
pub struct IterZeros<'a, T> {
    iter: core::slice::Iter<'a, T>,
    current: Option<(T, u32)>,
}

impl<'a, T> IterZeros<'a, T>
where
    T: Copy,
{
    pub(crate) fn new(mut iter: core::slice::Iter<'a, T>) -> Self {
        let current = iter.next().map(|v| (*v, 0));
        Self { iter, current }
    }
}

impl<'a, T> Iterator for IterZeros<'a, T>
where
    T: BitsOwned + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (bits, offset) = self.current.as_mut()?;

            if !bits.is_ones() {
                let index = bits.leading_ones();
                bits.bit_set(index);
                return Some(*offset + index);
            }

            self.current = Some((*self.iter.next()?, *offset + T::BITS));
        }
    }
}
