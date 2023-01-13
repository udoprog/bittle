use crate::bits::Bits;
use crate::endian::{BigEndian, Endian, LittleEndian};

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
/// [`BitsOwned`]: crate::BitsOwned
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
/// b.set_bit(111);
/// assert!(a.iter_ones().eq(b.iter_ones()));
/// ```
pub trait BitsMut: Bits {
    /// Set the given bit.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    fn set_bit_in<E>(&mut self, index: u32)
    where
        E: Endian;

    /// Set the given bit using [`DefaultEndian`].
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.test_bit(32));
    /// a.set_bit(0);
    /// assert!(a.test_bit(32));
    /// a.clear_bit(32);
    /// assert!(!a.test_bit(0));
    /// ```
    ///
    /// Using a bigger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.test_bit(0));
    /// assert!(a.test_bit(1));
    /// assert!(a.test_bit(127));
    ///
    /// a.clear_bit(1);
    ///
    /// assert!(a.test_bit(0));
    /// assert!(!a.test_bit(1));
    /// assert!(a.test_bit(127));
    ///
    /// a.set_bit(1);
    ///
    /// assert!(a.test_bit(0));
    /// assert!(a.test_bit(1));
    /// assert!(a.test_bit(127));
    /// ```
    fn set_bit(&mut self, index: u32);

    /// Set the given bit using [`LittleEndian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.test_bit_le(32));
    /// a.set_bit_le(0);
    /// assert!(a.test_bit_le(32));
    /// a.clear_bit_le(32);
    /// assert!(!a.test_bit_le(0));
    /// ```
    ///
    /// Using a bigger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.test_bit_le(0));
    /// assert!(a.test_bit_le(1));
    /// assert!(a.test_bit_le(127));
    ///
    /// a.clear_bit_le(1);
    ///
    /// assert!(a.test_bit_le(0));
    /// assert!(!a.test_bit_le(1));
    /// assert!(a.test_bit_le(127));
    ///
    /// a.set_bit_le(1);
    ///
    /// assert!(a.test_bit_le(0));
    /// assert!(a.test_bit_le(1));
    /// assert!(a.test_bit_le(127));
    /// ```
    #[inline]
    fn set_bit_le(&mut self, index: u32) {
        self.set_bit_in::<LittleEndian>(index);
    }

    /// Set the given bit using [`LittleEndian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.test_bit_be(32));
    /// a.set_bit_be(0);
    /// assert!(a.test_bit_be(32));
    /// a.clear_bit_be(32);
    /// assert!(!a.test_bit_be(0));
    /// ```
    ///
    /// Using a bigger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.test_bit_be(0));
    /// assert!(a.test_bit_be(1));
    /// assert!(a.test_bit_be(127));
    ///
    /// a.clear_bit_be(1);
    ///
    /// assert!(a.test_bit_be(0));
    /// assert!(!a.test_bit_be(1));
    /// assert!(a.test_bit_be(127));
    ///
    /// a.set_bit_be(1);
    ///
    /// assert!(a.test_bit_be(0));
    /// assert!(a.test_bit_be(1));
    /// assert!(a.test_bit_be(127));
    /// ```
    #[inline]
    fn set_bit_be(&mut self, index: u32) {
        self.set_bit_in::<BigEndian>(index);
    }

    /// Clear the given bit with a custom [`Endian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    fn clear_bit_in<E>(&mut self, index: u32)
    where
        E: Endian;

    /// Clear the given bit using [`DefaultEndian`].
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.test_bit(32));
    /// a.set_bit(0);
    /// assert!(a.test_bit(32));
    /// a.clear_bit(32);
    /// assert!(!a.test_bit(0));
    /// ```
    ///
    /// Example using array:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.test_bit(0));
    /// assert!(a.test_bit(1));
    /// assert!(a.test_bit(127));
    ///
    /// a.clear_bit(1);
    ///
    /// assert!(a.test_bit(0));
    /// assert!(!a.test_bit(1));
    /// assert!(a.test_bit(127));
    ///
    /// a.set_bit(1);
    ///
    /// assert!(a.test_bit(0));
    /// assert!(a.test_bit(1));
    /// assert!(a.test_bit(127));
    /// ```
    fn clear_bit(&mut self, index: u32);

    /// Clear the given bit using [`LittleEndian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.test_bit_le(32));
    /// a.set_bit_le(0);
    /// assert!(a.test_bit_le(32));
    /// a.clear_bit_le(32);
    /// assert!(!a.test_bit_le(0));
    /// ```
    ///
    /// Example using array:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.test_bit_le(0));
    /// assert!(a.test_bit_le(1));
    /// assert!(a.test_bit_le(127));
    ///
    /// a.clear_bit_le(1);
    ///
    /// assert!(a.test_bit_le(0));
    /// assert!(!a.test_bit_le(1));
    /// assert!(a.test_bit_le(127));
    ///
    /// a.set_bit_le(1);
    ///
    /// assert!(a.test_bit_le(0));
    /// assert!(a.test_bit_le(1));
    /// assert!(a.test_bit_le(127));
    /// ```
    #[inline]
    fn clear_bit_le(&mut self, index: u32) {
        self.clear_bit_in::<LittleEndian>(index);
    }

    /// Clear the given bit using [`BigEndian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = 0u32;
    /// assert!(!a.test_bit_be(32));
    /// a.set_bit_be(0);
    /// assert!(a.test_bit_be(32));
    /// a.clear_bit_be(32);
    /// assert!(!a.test_bit_be(0));
    /// ```
    ///
    /// Example using array:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.test_bit_be(0));
    /// assert!(a.test_bit_be(1));
    /// assert!(a.test_bit_be(127));
    ///
    /// a.clear_bit_be(1);
    ///
    /// assert!(a.test_bit_be(0));
    /// assert!(!a.test_bit_be(1));
    /// assert!(a.test_bit_be(127));
    ///
    /// a.set_bit_be(1);
    ///
    /// assert!(a.test_bit_be(0));
    /// assert!(a.test_bit_be(1));
    /// assert!(a.test_bit_be(127));
    /// ```
    #[inline]
    fn clear_bit_be(&mut self, index: u32) {
        self.clear_bit_in::<BigEndian>(index);
    }

    /// Clear the entire bit pattern.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut a = u128::ones();
    ///
    /// assert!(a.test_bit(0));
    /// assert!(a.test_bit(1));
    /// assert!(a.test_bit(127));
    ///
    /// a.clear_bits();
    ///
    /// assert!(!a.test_bit(0));
    /// assert!(!a.test_bit(1));
    /// assert!(!a.test_bit(127));
    ///
    /// a.set_bit(1);
    ///
    /// assert!(!a.test_bit(0));
    /// assert!(a.test_bit(1));
    /// assert!(!a.test_bit(127));
    /// ```
    fn clear_bits(&mut self);

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
    /// This keeps the elements in the first set which are not part of the
    /// second.
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
    /// assert!(c.iter_ones().eq([67]));
    /// assert!(d.iter_ones().eq([62]));
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
    /// assert!(c.iter_ones().eq([67]));
    /// assert!(d.iter_ones().eq([62]));
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
    fn set_bit_in<E>(&mut self, index: u32)
    where
        E: Endian,
    {
        (**self).set_bit_in::<E>(index);
    }

    #[inline]
    fn set_bit(&mut self, index: u32) {
        (**self).set_bit(index);
    }

    #[inline]
    fn clear_bit_in<E>(&mut self, index: u32)
    where
        E: Endian,
    {
        (**self).clear_bit_in::<E>(index);
    }

    #[inline]
    fn clear_bit(&mut self, index: u32) {
        (**self).clear_bit(index);
    }

    #[inline]
    fn clear_bits(&mut self) {
        (**self).clear_bits();
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
