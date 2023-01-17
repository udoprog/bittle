use crate::bits_mut::BitsMut;
use crate::endian::{BigEndian, Endian, LittleEndian};

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

    /// Owning iterator over bits set to ones using [`DefaultEndian`] indexing.
    ///
    /// See [`BitsOwned::into_iter_ones`].
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    type IntoIterOnes: Iterator<Item = u32>;

    /// Owning iterator over bits set to ones using custom [`Endian`] indexing.
    ///
    /// See [`BitsOwned::into_iter_ones_in`].
    type IntoIterOnesIn<E>: Iterator<Item = u32>
    where
        E: Endian;

    /// Owning iterator over bits set to zero using the [`DefaultEndian`] ordering.
    ///
    /// See [`BitsOwned::into_iter_zeros`].
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    type IntoIterZeros: Iterator<Item = u32>;

    /// Owning iterator over bits set to zero using custom [`Endian`] ordering.
    ///
    /// See [`BitsOwned::into_iter_zeros_in`].
    type IntoIterZerosIn<E>: Iterator<Item = u32>
    where
        E: Endian;

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
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let set = u128::zeros().with_bit_in::<LittleEndian>(8).with_bit_in::<LittleEndian>(12);
    /// assert!(set.iter_ones_in::<LittleEndian>().eq([8, 12]))
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let set = <[u32; 4]>::zeros().with_bit_in::<LittleEndian>(8).with_bit_in::<LittleEndian>(12);
    /// assert!(set.iter_ones_in::<LittleEndian>().eq([8, 12]))
    /// ```
    #[must_use]
    fn with_bit_in<E>(self, bit: u32) -> Self
    where
        E: Endian;

    /// Set the given bit and return the modified set with the [`DefaultEndian`]
    /// indexing.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
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
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u32; 4]>::zeros().with_bit(8).with_bit(12);
    /// assert!(set.iter_ones().eq([8, 12]))
    /// ```
    #[must_use]
    fn with_bit(self, bit: u32) -> Self;

    /// Set the given bit and return the modified set with the [`LittleEndian`] indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u128::zeros().with_bit_le(8).with_bit_le(12);
    /// assert!(set.iter_ones_le().eq([8, 12]))
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u32; 4]>::zeros().with_bit_le(8).with_bit_le(12);
    /// assert!(set.iter_ones_le().eq([8, 12]))
    /// ```
    #[must_use]
    #[inline]
    fn with_bit_le(self, bit: u32) -> Self
    where
        Self: Sized,
    {
        self.with_bit_in::<LittleEndian>(bit)
    }

    /// Set the given bit and return the modified set with the [`BigEndian`]
    /// indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u128::zeros().with_bit_be(8).with_bit_be(12);
    /// assert!(set.iter_ones_be().eq([8, 12]))
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u32; 4]>::zeros().with_bit_be(8).with_bit_be(12);
    /// assert!(set.iter_ones_be().eq([8, 12]))
    /// ```
    #[must_use]
    #[inline]
    fn with_bit_be(self, bit: u32) -> Self
    where
        Self: Sized,
    {
        self.with_bit_in::<BigEndian>(bit)
    }

    /// Set the given bit and return the modified set using custom [`Endian`]
    /// indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let set = u8::ones().without_bit_in::<LittleEndian>(2);
    /// assert!(set.iter_ones_in::<LittleEndian>().eq([0, 1, 3, 4, 5, 6, 7]))
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let set = <[u8; 2]>::ones().without_bit_in::<LittleEndian>(2).without_bit_in::<LittleEndian>(10);
    /// assert!(set.iter_ones_in::<LittleEndian>().eq([0, 1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]))
    /// ```
    #[must_use]
    fn without_bit_in<E>(self, bit: u32) -> Self
    where
        E: Endian;

    /// Set the given bit and return the modified set using [`DefaultEndian`]
    /// indexing.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
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
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u8; 2]>::ones().without_bit(2).without_bit(10);
    /// assert!(set.iter_ones().eq([0, 1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]))
    /// ```
    #[must_use]
    fn without_bit(self, bit: u32) -> Self;

    /// Set the given bit and return the modified set using [`LittleEndian`]
    /// indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u8::ones().without_bit_le(2);
    /// assert!(set.iter_ones_le().eq([0, 1, 3, 4, 5, 6, 7]))
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u8; 2]>::ones().without_bit_le(2).without_bit_le(10);
    /// assert!(set.iter_ones_le().eq([0, 1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]))
    /// ```
    #[must_use]
    #[inline]
    fn without_bit_le(self, bit: u32) -> Self
    where
        Self: Sized,
    {
        self.without_bit_in::<LittleEndian>(bit)
    }

    /// Set the given bit and return the modified set using [`BigEndian`]
    /// indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = u8::ones().without_bit_be(2);
    /// assert!(set.iter_ones_be().eq([0, 1, 3, 4, 5, 6, 7]))
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let set = <[u8; 2]>::ones().without_bit_be(2).without_bit_be(10);
    /// assert!(set.iter_ones_be().eq([0, 1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]))
    /// ```
    #[must_use]
    #[inline]
    fn without_bit_be(self, bit: u32) -> Self
    where
        Self: Sized,
    {
        self.without_bit_in::<BigEndian>(bit)
    }

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
    /// Using a larger set:
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
    /// Using a larger set:
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
    /// This returns the elements in the first set which are not part of the
    /// second.
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
    /// assert!(c.iter_ones().eq([67]));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.difference(b);
    /// assert!(c.iter_ones().eq([67]));
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
    /// Using a larger set:
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

    /// Construct an owning iterator over all ones in a set using the
    /// [`DefaultEndian`] indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
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
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![4, 63, 71, 127];
    /// assert!(a.into_iter_ones().eq([4, 63, 71, 127]));
    /// assert!(a.into_iter_ones().rev().eq([127, 71, 63, 4]));
    /// ```
    fn into_iter_ones(self) -> Self::IntoIterOnes;

    /// Construct an owning iterator over all ones in a set using custom
    /// [`Endian`] indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let a: u128 = bittle::set_le![3, 7];
    /// assert!(a.into_iter_ones_in::<LittleEndian>().eq([3, 7]));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let a: [u32; 4] = bittle::set_le![4, 63, 71];
    /// assert!(a.into_iter_ones_in::<LittleEndian>().eq([4, 63, 71]));
    /// ```
    fn into_iter_ones_in<E>(self) -> Self::IntoIterOnesIn<E>
    where
        E: Endian;

    /// Construct an owning iterator over all ones in a set using
    /// [`LittleEndian`] indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u128 = bittle::set_le![3, 7];
    /// assert!(a.into_iter_ones_le().eq([3, 7]));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set_le![4, 63, 71];
    /// assert!(a.into_iter_ones_le().eq([4, 63, 71]));
    /// ```
    #[inline]
    fn into_iter_ones_le(self) -> Self::IntoIterOnesIn<LittleEndian>
    where
        Self: Sized,
    {
        self.into_iter_ones_in()
    }

    /// Construct an owning iterator over all ones in a set using [`BigEndian`]
    /// indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u128 = bittle::set![3, 7];
    /// assert!(a.into_iter_ones_be().eq([3, 7]));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u32; 4] = bittle::set![4, 63, 71];
    /// assert!(a.into_iter_ones_be().eq([4, 63, 71]));
    /// ```
    #[inline]
    fn into_iter_ones_be(self) -> Self::IntoIterOnesIn<BigEndian>
    where
        Self: Sized,
    {
        self.into_iter_ones_in()
    }

    /// Construct an owning iterator over all zeros in a set using
    /// [`DefaultEndian`] indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
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
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u8; 2] = bittle::set![4, 7, 10];
    /// assert!(a.into_iter_zeros().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// assert!(a.into_iter_zeros().rev().eq([15, 14, 13, 12, 11, 9, 8, 6, 5, 3, 2, 1, 0]));
    /// ```
    fn into_iter_zeros(self) -> Self::IntoIterZeros;

    /// Construct an owning iterator over all zeros in a set using custom
    /// [`Endian`] indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let a: u16 = bittle::set_le![4, 7, 10];
    /// assert!(a.into_iter_zeros_in::<LittleEndian>().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned, LittleEndian};
    ///
    /// let a: [u8; 2] = bittle::set_le![4, 7, 10];
    /// assert!(a.into_iter_zeros_in::<LittleEndian>().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    fn into_iter_zeros_in<E>(self) -> Self::IntoIterZerosIn<E>
    where
        E: Endian;

    /// Construct an owning iterator over all zeros in a set using
    /// [`LittleEndian`] indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u16 = bittle::set_le![4, 7, 10];
    /// assert!(a.into_iter_zeros_le().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u8; 2] = bittle::set_le![4, 7, 10];
    /// assert!(a.into_iter_zeros_le().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    #[inline]
    fn into_iter_zeros_le(self) -> Self::IntoIterZerosIn<LittleEndian>
    where
        Self: Sized,
    {
        self.into_iter_zeros_in()
    }

    /// Construct an owning iterator over all zeros in a set using [`BigEndian`]
    /// indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: u16 = bittle::set![4, 7, 10];
    /// assert!(a.into_iter_zeros_be().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsOwned};
    ///
    /// let a: [u8; 2] = bittle::set![4, 7, 10];
    /// assert!(a.into_iter_zeros_be().eq([0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15]));
    /// ```
    #[inline]
    fn into_iter_zeros_be(self) -> Self::IntoIterZerosIn<BigEndian>
    where
        Self: Sized,
    {
        self.into_iter_zeros_in()
    }
}
