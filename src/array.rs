//! [Bits] implementation and associated types for arrays.

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::number::Number;
use crate::slice::{IterOnes, IterZeros};

impl<T, const N: usize> BitsOwned for [T; N]
where
    T: Eq + BitsOwned + Number,
{
    #[allow(clippy::cast_possible_truncation)]
    const BITS: u32 = match T::BITS.checked_mul(N as u32) {
        Some(value) => value,
        None => panic!("32-bit overflow in capacity"),
    };
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
    fn with_bit(mut self, bit: u32) -> Self {
        self[(bit / T::BITS) as usize % N].set_bit(bit % T::BITS);
        self
    }

    #[inline]
    fn without_bit(mut self, bit: u32) -> Self {
        self[(bit / T::BITS) as usize % N].clear_bit(bit % T::BITS);
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
    T: Eq + BitsOwned + Number,
{
    type IterOnes<'a> = IterOnes<'a, T> where Self: 'a;
    type IterZeros<'a> = IterZeros<'a, T> where Self: 'a;

    #[inline]
    fn count_ones(&self) -> u32 {
        self.iter().map(Bits::count_ones).sum()
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
    fn test_bit(&self, index: u32) -> bool {
        self[(index / T::BITS) as usize % N].test_bit(index % T::BITS)
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

impl<T, const N: usize> BitsMut for [T; N]
where
    T: Eq + BitsOwned + Number,
{
    #[inline]
    fn set_bit(&mut self, index: u32) {
        self[(index / T::BITS) as usize % N].set_bit(index % T::BITS);
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

/// An owned iterator over the bits set to ones in an array.
#[derive(Clone)]
pub struct IntoIterOnes<T, const N: usize> {
    iter: core::array::IntoIter<T, N>,
    current: Option<(T, u32)>,
}

impl<T, const N: usize> Iterator for IntoIterOnes<T, N>
where
    T: BitsOwned + Number,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some((bits, offset)) = &mut self.current else {
                return None;
            };

            if !bits.all_zeros() {
                let index = T::leading_zeros(*bits);
                bits.clear_bit(index);
                return Some(*offset + index);
            }

            self.current = Some((self.iter.next()?, *offset + T::BITS));
        }
    }
}
