use crate::bits::Bits;

/// Bitset mutable operations.
///
/// This is implemented for primitive types such as:
/// * [`usize`], [`u32`], [`u64`], and other signed numbers.
/// * Arrays made up of numerical primitives, such as `[u32; 32]`.
/// * Slices of numerical primitives, such as `&[u32]`.
///
/// Also see the associated sibling traits:
///
/// * [`Bits`] for immutable operations.
/// * [`BitsOwned`] for owned operations.
///
/// [Bits]: crate::Bits
/// [BitsOwned]: crate::BitsOwned
///
/// # Examples
///
/// We can use the iterator of each set to compare bit sets of different kinds.
/// The [`Bits::iter_ones`] iterator is guaranteed to iterate elements in the
/// same order:
///
/// ```
/// use bittle::{Bits, BitsMut};
///
/// let a: [u64; 2] = bittle::set![111];
/// let mut b = 0u128;
///
/// assert!(!a.iter_ones().eq(b.iter_ones()));
/// b.bit_set(111);
/// assert!(a.iter_ones().eq(b.iter_ones()));
/// ```
pub trait BitsMut: Bits {
    /// Set the given bit.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.bit_test(32));
    /// a.bit_set(0);
    /// assert!(a.bit_test(32));
    /// a.bit_clear(32);
    /// assert!(!a.bit_test(0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.bit_test(0));
    /// assert!(a.bit_test(1));
    /// assert!(a.bit_test(127));
    ///
    /// a.bit_clear(1);
    ///
    /// assert!(a.bit_test(0));
    /// assert!(!a.bit_test(1));
    /// assert!(a.bit_test(127));
    ///
    /// a.bit_set(1);
    ///
    /// assert!(a.bit_test(0));
    /// assert!(a.bit_test(1));
    /// assert!(a.bit_test(127));
    /// ```
    fn bit_set(&mut self, index: u32);

    /// Unset the given bit.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.bit_test(32));
    /// a.bit_set(0);
    /// assert!(a.bit_test(32));
    /// a.bit_clear(32);
    /// assert!(!a.bit_test(0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.bit_test(0));
    /// assert!(a.bit_test(1));
    /// assert!(a.bit_test(127));
    ///
    /// a.bit_clear(1);
    ///
    /// assert!(a.bit_test(0));
    /// assert!(!a.bit_test(1));
    /// assert!(a.bit_test(127));
    ///
    /// a.bit_set(1);
    ///
    /// assert!(a.bit_test(0));
    /// assert!(a.bit_test(1));
    /// assert!(a.bit_test(127));
    /// ```
    fn bit_clear(&mut self, index: u32);

    /// Clear the entire bit pattern.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.bit_test(0));
    /// assert!(a.bit_test(1));
    /// assert!(a.bit_test(127));
    ///
    /// a.bits_clear();
    ///
    /// assert!(!a.bit_test(0));
    /// assert!(!a.bit_test(1));
    /// assert!(!a.bit_test(127));
    ///
    /// a.bit_set(1);
    ///
    /// assert!(!a.bit_test(0));
    /// assert!(a.bit_test(1));
    /// assert!(!a.bit_test(127));
    /// ```
    fn bits_clear(&mut self);

    /// Modify the current set in place so that it becomes a union of this and
    /// another set.
    ///
    /// A union retains all elements from both sets.
    ///
    /// In terms of numerical operations, this is equivalent to
    /// [`BitOrAssign`][core::ops::BitOrAssign] or `a |= b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// a.union_assign(&b);
    ///
    /// assert!(a.iter_ones().eq([31, 62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// a.union_assign(&b);
    ///
    /// assert!(a.iter_ones().eq([31, 62, 67]));
    /// ```
    fn union_assign(&mut self, other: &Self);

    /// Modify the current set in place so that it becomes a conjunction of this
    /// and another set.
    ///
    /// A conjunction keeps the elements which are in common between two sets.
    ///
    /// In terms of numerical operations, this is equivalent to
    /// [`BitAndAssign`][core::ops::BitAndAssign] or `a &= b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// a.conjunction_assign(&b);
    ///
    /// assert!(a.iter_ones().eq([31]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// a.conjunction_assign(&b);
    ///
    /// assert!(a.iter_ones().eq([31]));
    /// ```
    fn conjunction_assign(&mut self, other: &Self);

    /// Modify the current set in place so that it becomes a difference of this
    /// and another set.
    ///
    /// This assigns the elements in the second set which are not part of the
    /// first.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let mut c = a;
    /// c.difference_assign(&b);
    ///
    /// let mut d = b;
    /// d.difference_assign(&a);
    ///
    /// assert_ne!(c, d);
    ///
    /// assert!(c.iter_ones().eq([62]));
    /// assert!(d.iter_ones().eq([67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let mut c = a;
    /// c.difference_assign(&b);
    ///
    /// let mut d = b;
    /// d.difference_assign(&a);
    ///
    /// assert_ne!(c, d);
    ///
    /// assert!(c.iter_ones().eq([62]));
    /// assert!(d.iter_ones().eq([67]));
    /// ```
    fn difference_assign(&mut self, other: &Self);

    /// Modify the current set in place so that it becomes a symmetric
    /// difference of this and another set.
    ///
    /// This retains elements which are unique to each set.
    ///
    /// In terms of numerical operations, this is equivalent to
    /// [`BitXorAssign`][core::ops::BitXorAssign] or `a ^= b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// a.symmetric_difference_assign(&b);
    ///
    /// assert!(a.iter_ones().eq([62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// a.symmetric_difference_assign(&b);
    ///
    /// assert!(a.iter_ones().eq([62, 67]));
    /// ```
    fn symmetric_difference_assign(&mut self, other: &Self);
}

impl<T> BitsMut for &mut T
where
    T: ?Sized + BitsMut,
{
    #[inline]
    fn bit_set(&mut self, index: u32) {
        (**self).bit_set(index);
    }

    #[inline]
    fn bit_clear(&mut self, index: u32) {
        (**self).bit_clear(index);
    }

    #[inline]
    fn bits_clear(&mut self) {
        (**self).bits_clear();
    }

    #[inline]
    fn union_assign(&mut self, other: &Self) {
        (**self).union_assign(other);
    }

    #[inline]
    fn conjunction_assign(&mut self, other: &Self) {
        (**self).conjunction_assign(other);
    }

    #[inline]
    fn difference_assign(&mut self, other: &Self) {
        (**self).difference_assign(other);
    }

    #[inline]
    fn symmetric_difference_assign(&mut self, other: &Self) {
        (**self).symmetric_difference_assign(other);
    }
}
