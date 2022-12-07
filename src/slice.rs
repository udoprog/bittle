//! [Bits] associated types for slices.

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
    fn all_zeros(&self) -> bool {
        self.iter().all(Bits::all_zeros)
    }

    #[inline]
    fn all_ones(&self) -> bool {
        self.iter().all(Bits::all_ones)
    }

    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        self[((index / T::BITS) as usize % self.len())].test_bit(index % T::BITS)
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
    fn set_bit(&mut self, index: u32) {
        self[((index / T::BITS) as usize % self.len())].set_bit(index % T::BITS);
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
    fn clear_bit(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.clear_bit(index % T::BITS);
        }
    }

    #[inline]
    fn clear_bits(&mut self) {
        for b in self {
            b.clear_bits();
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

            if !bits.all_zeros() {
                let index = bits.leading_zeros();
                bits.clear_bit(index);
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

            if !bits.all_ones() {
                let index = bits.leading_ones();
                bits.set_bit(index);
                return Some(*offset + index);
            }

            self.current = Some((*self.iter.next()?, *offset + T::BITS));
        }
    }
}
