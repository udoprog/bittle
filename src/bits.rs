//! Traits which define the behaviors of a bit set.

/// Bitset operations.
///
/// This is implemented for primitive types such as:
/// * [`usize`], [`u32`], [`u64`], and other signed numbers.
/// * Arrays made up of numerical primitives, such as `[u32; 32]`.
/// * Slices of numerical primitives, such as `&[u32]`.
///
/// This does not include owned operations such as turning the bit set into an
/// owned iterator using [OwnedBits::into_iter_ones], for more like that see
/// [OwnedBits].
///
/// # Examples
///
/// We can use the iterator of each set to compare bit sets of different kinds.
/// The [Bits::iter_ones] iterator is guaranteed to iterate elements in the same
/// order:
///
/// ```
/// use bittle::Bits;
///
/// let a: [u64; 2] = bittle::set![111];
/// let mut b = 0u128;
///
/// assert!(!a.iter_ones().eq(b.iter_ones()));
/// b.bit_set(111);
/// assert!(a.iter_ones().eq(b.iter_ones()));
/// ```
pub trait Bits {
    /// The iterator over this bit pattern.
    ///
    /// See [Bits::iter_ones].
    type IterOnes<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    /// Get the length of the bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a = 0u128;
    /// assert_eq!(a.bits_len(), 0);
    /// a.bit_set(4);
    /// assert_eq!(a.bits_len(), 1);
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a = [0u128, 0];
    /// assert_eq!(a.bits_len(), 0);
    /// a.bit_set(240);
    /// assert_eq!(a.bits_len(), 1);
    /// ```
    fn bits_len(&self) -> u32;

    /// Get the bits_capacity of the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = 0u128;
    /// assert_eq!(set.bits_capacity(), 128);
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = [0u128, 0];
    /// assert_eq!(set.bits_capacity(), 256);
    /// ```
    fn bits_capacity(&self) -> u32;

    /// Test if this set is empty, or all zeros.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a = 0u128;
    /// assert!(a.is_zeros());
    /// a.bit_set(4);
    /// assert!(!a.is_zeros());
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a = [0u128; 2];
    /// assert!(a.is_zeros());
    /// a.bit_set(250);
    /// assert!(!a.is_zeros());
    /// ```
    fn is_zeros(&self) -> bool;

    /// Test if bit set is full, or all ones.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u128::ones();
    /// assert!(set.is_ones());
    /// set.bit_clear(4);
    /// assert!(!set.is_ones());
    /// ```
    fn is_ones(&self) -> bool;

    /// Test if the given bit is set.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
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
    /// use bittle::{Bits, OwnedBits};
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
    /// ```
    fn bit_test(&self, index: u32) -> bool;

    /// Set the given bit.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
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
    /// use bittle::{Bits, OwnedBits};
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
    /// use bittle::{Bits, OwnedBits};
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
    /// use bittle::{Bits, OwnedBits};
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
    /// use bittle::{Bits, OwnedBits};
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
    /// use bittle::Bits;
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
    /// use bittle::Bits;
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
    /// use bittle::Bits;
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
    /// use bittle::Bits;
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
    /// use bittle::Bits;
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
    /// use bittle::Bits;
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
    /// use bittle::Bits;
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
    /// use bittle::Bits;
    ///
    /// let mut a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// a.symmetric_difference_assign(&b);
    ///
    /// assert!(a.iter_ones().eq([62, 67]));
    /// ```
    fn symmetric_difference_assign(&mut self, other: &Self);

    /// Construct an iterator over ones that are set in the bit set.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: u128 = bittle::set![3, 7];
    /// assert!(set.iter_ones().eq([3, 7]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: [u32; 4] = bittle::set![4, 67, 71];
    /// assert!(set.iter_ones().eq([4, 67, 71]));
    /// ```
    fn iter_ones(&self) -> Self::IterOnes<'_>;

    /// Join this bit set with an iterator, creating an iterator that only
    /// yields the elements which are set to ones.
    ///
    /// The underlying iterator is advanced using [`Iterator::nth`] as
    /// appropriate.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mask: u128 = bittle::set![0, 1, 3];
    /// let mut values = vec![false, false, false, false];
    ///
    /// for value in mask.join_ones(values.iter_mut()) {
    ///     *value = true;
    /// }
    ///
    /// assert_eq!(values, vec![true, true, false, true]);
    /// ```
    fn join_ones<I>(&self, iter: I) -> JoinOnes<Self::IterOnes<'_>, I::IntoIter>
    where
        Self: Sized,
        I: IntoIterator,
    {
        JoinOnes {
            mask: self.iter_ones(),
            right: iter.into_iter(),
            last: 0,
        }
    }
}

/// A joined iterator.
///
/// Created using [Mask::join_ones].
pub struct JoinOnes<A, B> {
    mask: A,
    right: B,
    last: u32,
}

impl<A, B> Iterator for JoinOnes<A, B>
where
    A: Iterator<Item = u32>,
    B: Iterator,
{
    type Item = B::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.mask.next()?;
        let offset = index - self.last;
        let buf = self.right.nth(offset as usize)?;
        self.last = index + 1;
        Some(buf)
    }
}
