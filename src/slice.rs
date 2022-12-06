//! [Bits] implementation and associated types for slices.

use crate::bits::Bits;
use crate::number::Number;

impl<T> Bits for [T]
where
    T: Number,
{
    type BitsIter<'a> = BitsIter<'a, T> where Self: 'a;

    #[inline]
    fn is_empty(&self) -> bool {
        self.iter().all(|b| b.is_empty())
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.iter().all(|b| b.is_full())
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
    fn bits(&self) -> Self::BitsIter<'_> {
        BitsIter::new(IntoIterator::into_iter(self))
    }
}

/// A borrowing iterator over the bits of a `[T; N]`.
#[derive(Clone)]
pub struct BitsIter<'a, T>
where
    T: Number,
{
    iter: core::slice::Iter<'a, T>,
    current: Option<(T, u32)>,
}

impl<'a, T> BitsIter<'a, T>
where
    T: Number,
{
    pub(crate) fn new(mut iter: core::slice::Iter<'a, T>) -> Self {
        let current = iter.next().map(|v| (*v, 0));
        Self { iter, current }
    }
}

impl<'a, T> Iterator for BitsIter<'a, T>
where
    T: Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (bits, offset) = self.current.as_mut()?;

            if !bits.is_empty() {
                let index = bits.trailing_zeros();
                bits.unset(index);
                return Some(*offset + index);
            }

            self.current = Some((*self.iter.next()?, *offset + T::BITS));
        }
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

            self.current = Some((self.iter.next()?, *offset + T::BITS));
        }
    }
}
