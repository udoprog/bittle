use crate::bits_mut::BitsMut;

/// Bitset owned operations.
///
/// This is implemented for primitive types such as:
/// * [`usize`], [`u32`], [`u64`], and other signed numbers.
/// * Arrays made up of numerical primitives, such as `[u32; 32]`.
///
/// In contrast to [`Bits`] and [`BitsMut`] this is not implemented for slices
/// such as `&[u32]`. This is since the operations provided here require
/// ownership of the underlying data.
///
/// Also see the associated sibling traits:
///
/// * [`Bits`] for immutable operations.
/// * [`BitsMut`] for mutable operations.
///
/// [`Bits`]: crate::Bits
///
/// # Examples
///
/// ```
/// use bittle::{Bits, BitsOwned};
///
/// let a = u128::zeros();
/// let b = bittle::set!(77);
///
/// assert!(!a.test_bit(77));
/// assert!(a.union(b).test_bit(77));
/// ```
///
/// The bit set can also use arrays as its backing storage.
///
/// ```
/// use bittle::{Bits, BitsOwned};
///
/// let a = <[u32; 4]>::zeros();
/// let b = bittle::set!(77);
///
/// assert!(!a.test_bit(77));
/// assert!(a.union(b).test_bit(77));
/// ```
pub trait BitsOwned: BitsMut {
    /// The number of bits in the bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::BitsOwned;
    ///
    /// assert_eq!(u32::BITS, 32);
    /// assert_eq!(<[u32; 4]>::BITS, 128);
    /// ```
    const BITS: u32;

    /// The bit pattern containing all zeros, or one that is empty.
    ///
    /// See [`BitsOwned::zeros`].
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::BitsOwned;
    ///
    /// assert_eq!(u32::ZEROS, 0);
    /// assert_eq!(<[u32; 4]>::ZEROS, [0, 0, 0, 0]);
    /// ```
    const ZEROS: Self;

    /// The bit pattern containing all ones, or one that is full.
    ///
    /// See [`BitsOwned::ones`].
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::BitsOwned;
    ///
    /// assert_eq!(u32::ONES, u32::MAX);
    /// assert_eq!(<[u32; 4]>::ONES, [u32::MAX, u32::MAX, u32::MAX, u32::MAX]);
    /// ```
    const ONES: Self;

    /// Owning iterator over bits set to one.
    ///
    /// See [`BitsOwned::into_iter_ones`].
    type IntoIterOnes: Iterator<Item = u32>;

    /// Owning iterator over bits set to zero.
    ///
    /// See [`BitsOwned::into_iter_zeros`].
    type IntoIterZeros: Iterator<Item = u32>;

    /// Construct a bit set of all zeros, or one that is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u128::zeros();
    /// assert!(set.all_zeros());
    /// assert_eq!(set.iter_ones().count(), 0);
    /// ```
    fn zeros() -> Self;

    /// Construct a bit set of all ones, or one that is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u128::ones();
    /// assert!(set.all_ones());
    /// assert!(set.iter_ones().eq(0..128))
    /// ```
    fn ones() -> Self;

    /// Set the given bit and return the modified set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u128::zeros().with_bit(8).with_bit(12);
    /// assert!(set.iter_ones().eq([8, 12]))
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u32; 4]>::zeros().with_bit(8).with_bit(12);
    /// assert!(set.iter_ones().eq([8, 12]))
    /// ```
    #[must_use]
    fn with_bit(self, bit: u32) -> Self;

    /// Set the given bit and return the modified set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u8::ones().without_bit(2);
    /// assert!(set.iter_ones().eq([0, 1, 3, 4, 5, 6, 7]))
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u8; 2]>::ones().without_bit(2).without_bit(10);
    /// assert!(set.iter_ones().eq([0, 1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]))
    /// ```
    #[must_use]
    fn without_bit(self, bit: u32) -> Self;

    /// Construct the union between this and another set.
    ///
    /// A union retains all elements from both sets.
    ///
    /// In terms of numerical operations, this is equivalent to
    /// [`BitOr`][core::ops::BitOr] or `a | b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.union(b);
    /// assert!(c.iter_ones().eq([31, 62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.union(b);
    /// assert!(c.iter_ones().eq([31, 62, 67]));
    /// ```
    #[must_use]
    fn union(self, other: Self) -> Self;

    /// Construct a conjunction of this and another set.
    ///
    /// A conjunction keeps the elements which are in common between two sets.
    ///
    /// In terms of numerical operations, this is equivalent to
    /// [`BitAnd`][core::ops::BitAnd] or `a & b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.conjunction(b);
    /// assert!(c.iter_ones().eq([31]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.conjunction(b);
    /// assert!(c.iter_ones().eq([31]));
    /// ```
    #[must_use]
    fn conjunction(self, other: Self) -> Self;

    /// Construct the difference between this and another set.
    ///
    /// This returns the elements in the second set which are not part of the
    /// first.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Set, Bits, BitsOwned};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.difference(b);
    /// assert!(c.iter_ones().eq([62]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.difference(b);
    /// assert!(c.iter_ones().eq([62]));
    /// ```
    #[must_use]
    fn difference(self, other: Self) -> Self;

    /// Construct the symmetric difference between this and another set.
    ///
    /// This retains elements which are unique to each set.
    ///
    /// In terms of numerical operations, this is equivalent to
    /// [`BitXor`][core::ops::BitXor] or `a ^ b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.symmetric_difference(b);
    /// assert!(c.iter_ones().eq([62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.symmetric_difference(b);
    /// assert!(c.iter_ones().eq([62, 67]));
    /// ```
    #[must_use]
    fn symmetric_difference(self, other: Self) -> Self;

    /// Construct an owning iterator over all ones in a set.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u128 = bittle::set![3, 7];
    /// assert!(a.into_iter_ones().eq([3, 7]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![4, 63, 71];
    /// assert!(a.into_iter_ones().eq([4, 63, 71]));
    /// ```
    fn into_iter_ones(self) -> Self::IntoIterOnes;

    /// Construct an owning iterator over all zeros in a set.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u16 = bittle::set![4, 7, 10];
    /// assert!(a.into_iter_zeros().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u8; 2] = bittle::set![4, 7, 10];
    /// assert!(a.into_iter_zeros().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    fn into_iter_zeros(self) -> Self::IntoIterZeros;
}
