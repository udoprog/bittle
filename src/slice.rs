//! [Bits] associated types for slices.

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::BitsOwned;

impl<T> Bits for [T]
where
    T: Copy + BitsOwned,
{
    type IterOnes<'a> = IterOnes<'a, T> where Self: 'a;
    type IterZeros<'a> = IterZeros<'a, T> where Self: 'a;

    /// Count the number of ones in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// let a = a.as_slice();
    /// assert_eq!(a.count_ones(), 3);
    /// ```
    #[inline]
    fn count_ones(&self) -> u32 {
        self.iter().map(Bits::count_ones).sum()
    }

    /// Count the number of zeros in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// let a = a.as_slice();
    /// assert_eq!(a.count_zeros(), 13);
    /// ```
    #[inline]
    fn count_zeros(&self) -> u32 {
        self.iter().map(Bits::count_zeros).sum()
    }

    /// Get the capacity of the slice.
    ///
    /// The capacity of a slice is determined by its length.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u8; 4] = bittle::set![4, 11, 14];
    /// let a = &a[..2];
    /// assert_eq!(a.bits_capacity(), <[u8; 2]>::BITS);
    /// ```
    #[inline]
    fn bits_capacity(&self) -> u32 {
        let len = u32::try_from(self.len()).unwrap_or(u32::MAX);
        len.saturating_mul(T::BITS)
    }

    /// Test if the slice is all zeros.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a = <[u8; 2]>::zeros();
    /// let a = a.as_slice();
    /// assert!(a.all_zeros());
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// let a = a.as_slice();
    /// assert!(!a.all_zeros());
    /// ```
    #[inline]
    fn all_zeros(&self) -> bool {
        self.iter().all(Bits::all_zeros)
    }

    /// Test if the slice is all ones.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a = <[u8; 2]>::ones();
    /// let a = a.as_slice();
    /// assert!(a.all_ones());
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// let a = a.as_slice();
    /// assert!(!a.all_ones());
    /// ```
    #[inline]
    fn all_ones(&self) -> bool {
        self.iter().all(Bits::all_ones)
    }

    /// Test if the given bit is set in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u8; 2] = bittle::set![4, 11, 14];
    /// let a: &[u8] = a.as_slice();
    /// assert!(a.test_bit(4));
    /// ```
    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        self[((index / T::BITS) as usize % self.len())].test_bit(index % T::BITS)
    }

    /// Iterates over all ones in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u8; 2] = bittle::set![4, 11, 14];
    /// let a: &[u8] = a.as_slice();
    /// assert!(a.iter_ones().eq([4, 11, 14]));
    /// ```
    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        IterOnes::new(IntoIterator::into_iter(self))
    }

    /// Iterates over all zeros in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u8; 2] = bittle::set![4, 11, 14];
    /// let a: &[u8] = a.as_slice();
    /// assert!(a.iter_zeros().eq([0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 15]));
    /// ```
    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        IterZeros::new(IntoIterator::into_iter(self))
    }
}

impl<T> BitsMut for [T]
where
    T: Copy + BitsOwned,
{
    /// Set the given bit is set in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: [u8; 2] = bittle::set![7];
    /// let a: &mut [u8] = a.as_mut_slice();
    /// a.set_bit(13);
    /// assert!(a.iter_ones().eq([7, 13]));
    /// ```
    #[inline]
    fn set_bit(&mut self, index: u32) {
        self[((index / T::BITS) as usize % self.len())].set_bit(index % T::BITS);
    }

    /// Set the given bit is set in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: [u8; 2] = bittle::set![7, 13];
    /// let a: &mut [u8] = a.as_mut_slice();
    /// a.clear_bit(13);
    /// assert!(a.iter_ones().eq([7]));
    /// ```
    #[inline]
    fn clear_bit(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.clear_bit(index % T::BITS);
        }
    }

    /// Clear the entire slice, or set all bits to zeros.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: [u8; 2] = bittle::set![7, 13];
    /// let a: &mut [u8] = a.as_mut_slice();
    /// a.clear_bits();
    /// assert!(a.all_zeros());
    /// ```
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

/// A borrowing iterator over the bits set to one in a slice.
#[derive(Clone)]
pub struct IterOnes<'a, T>
where
    T: Copy + BitsOwned,
{
    iter: core::slice::Iter<'a, T>,
    current: Option<(T::IntoIterOnes, u32)>,
}

impl<'a, T> IterOnes<'a, T>
where
    T: Copy + BitsOwned,
{
    #[inline]
    pub(crate) fn new(mut iter: core::slice::Iter<'a, T>) -> Self {
        let current = iter.next().map(|v| (v.into_iter_ones(), 0));
        Self { iter, current }
    }
}

impl<'a, T> Iterator for IterOnes<'a, T>
where
    T: Copy + BitsOwned,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some((it, offset)) = &mut self.current else {
                return None;
            };

            if let Some(index) = it.next() {
                return offset.checked_add(index);
            }

            self.current = Some((
                self.iter.next()?.into_iter_ones(),
                offset.checked_add(T::BITS)?,
            ));
        }
    }
}

/// A borrowing iterator over the bits set to one in a slice.
#[derive(Clone)]
pub struct IterZeros<'a, T>
where
    T: Copy + BitsOwned,
{
    iter: core::slice::Iter<'a, T>,
    current: Option<(T::IntoIterZeros, u32)>,
}

impl<'a, T> IterZeros<'a, T>
where
    T: Copy + BitsOwned,
{
    #[inline]
    pub(crate) fn new(mut iter: core::slice::Iter<'a, T>) -> Self {
        let current = iter.next().map(|v| (v.into_iter_zeros(), 0));
        Self { iter, current }
    }
}

impl<'a, T> Iterator for IterZeros<'a, T>
where
    T: Copy + BitsOwned,
{
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some((it, offset)) = &mut self.current else {
                return None;
            };

            if let Some(index) = it.next() {
                return offset.checked_add(index);
            }

            self.current = Some((
                self.iter.next()?.into_iter_zeros(),
                offset.checked_add(T::BITS)?,
            ));
        }
    }
}
