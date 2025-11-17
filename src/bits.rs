//! Traits which define the behaviors of a bit set.

mod join_ones;
use crate::endian::{BigEndian, DefaultEndian, Endian, LittleEndian};

pub use self::join_ones::JoinOnes;

mod sealed {
    pub trait Sealed {}

    impl<T> Sealed for &mut T where T: ?Sized + crate::Bits {}
    impl<T> Sealed for &T where T: ?Sized + crate::Bits {}
    impl<T> Sealed for [T] {}
    impl<T, const N: usize> Sealed for [T; N] {}
    impl<T, E> Sealed for crate::set::Set<T, E> where T: ?Sized {}
}

pub(crate) use self::sealed::Sealed;

/// Bitset immutable operations.
///
/// This is implemented for primitive types such as:
/// * [`usize`], [`u32`], [`u64`], and other signed numbers.
/// * Arrays made up of numerical primitives, such as `[u32; 32]`.
/// * Slices of numerical primitives, such as `&[u32]`.
///
/// Also see the associated sibling traits:
///
/// * [`BitsMut`] for mutable operations.
/// * [`BitsOwned`] for owned operations.
///
/// [`BitsMut`]: crate::BitsMut
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
pub trait Bits: Sealed {
    /// The iterator over ones in this bit pattern using [`DefaultEndian`]
    /// indexing.
    ///
    /// See [`Bits::iter_ones`].
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    type IterOnes<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    /// The iterator over ones in this bit pattern using custom [`Endian`]
    /// indexing.
    ///
    /// See [`Bits::iter_ones_in`].
    type IterOnesIn<'a, E>: Iterator<Item = u32>
    where
        Self: 'a,
        E: Endian;

    /// The iterator over zeros in this bit pattern using [`DefaultEndian`]
    /// indexing.
    ///
    /// See [`Bits::iter_zeros`].
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    type IterZeros<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    /// The iterator over zeros in this bit pattern using custom [`Endian`]
    /// indexing.
    ///
    /// See [`Bits::iter_zeros_in`].
    type IterZerosIn<'a, E>: Iterator<Item = u32>
    where
        Self: 'a,
        E: Endian;

    /// Get the number of ones in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a = 0u128;
    /// assert_eq!(a.count_ones(), 0);
    /// a.set_bit(4);
    /// assert_eq!(a.count_ones(), 1);
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a = [0u128, 0];
    /// assert_eq!(a.count_ones(), 0);
    /// a.set_bit(240);
    /// assert_eq!(a.count_ones(), 1);
    /// ```
    fn count_ones(&self) -> u32;

    /// Get the number of ones in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a = 0u128;
    /// assert_eq!(a.count_zeros(), 128);
    /// a.set_bit(4);
    /// assert_eq!(a.count_zeros(), 127);
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, BitsMut};
    ///
    /// let mut a = [0u128, 0];
    /// assert_eq!(a.count_zeros(), 256);
    /// a.set_bit(240);
    /// assert_eq!(a.count_zeros(), 255);
    /// ```
    fn count_zeros(&self) -> u32;

    /// Get the capacity of the underlying set.
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
    /// Using a larger set:
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
    /// let a: u32 = bittle::set![];
    /// assert!(a.all_zeros());
    ///
    /// let a: u32 = bittle::set![1];
    /// assert!(!a.all_zeros());
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u32; 2] = bittle::set![];
    /// assert!(a.all_zeros());
    ///
    /// let a: [u32; 2] = bittle::set![55];
    /// assert!(!a.all_zeros());
    /// ```
    fn all_zeros(&self) -> bool;

    /// Test if bit set is full, or all ones.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned};
    ///
    /// let mut set = u128::ones();
    /// assert!(set.all_ones());
    /// set.clear_bit(4);
    /// assert!(!set.all_ones());
    /// ```
    fn all_ones(&self) -> bool;

    /// Test if the given bit is set using [`DefaultEndian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: u32 = bittle::set![];
    /// assert!(!a.test_bit(32));
    ///
    /// let a: u32 = bittle::set![32];
    /// assert!(a.test_bit(32));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u32; 2] = bittle::set![];
    /// assert!(!a.test_bit(55));
    ///
    /// let a: [u32; 2] = bittle::set![55];
    /// assert!(a.test_bit(55));
    /// ```
    fn test_bit(&self, index: u32) -> bool;

    /// Test if the given bit is set using custom [`Endian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let a: u32 = bittle::set_le![];
    /// assert!(!a.test_bit_in::<LittleEndian>(32));
    ///
    /// let a: u32 = bittle::set_le![32];
    /// assert!(a.test_bit_in::<LittleEndian>(32));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let a: [u32; 2] = bittle::set_le![];
    /// assert!(!a.test_bit_in::<LittleEndian>(55));
    ///
    /// let a: [u32; 2] = bittle::set_le![55];
    /// assert!(a.test_bit_in::<LittleEndian>(55));
    /// ```
    fn test_bit_in<E>(&self, index: u32) -> bool
    where
        E: Endian;

    /// Test if the given bit is set using [`LittleEndian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: u32 = bittle::set_le![];
    /// assert!(!a.test_bit_le(32));
    ///
    /// let a: u32 = bittle::set_le![32];
    /// assert!(a.test_bit_le(32));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u32; 2] = bittle::set_le![];
    /// assert!(!a.test_bit_le(55));
    ///
    /// let a: [u32; 2] = bittle::set_le![55];
    /// assert!(a.test_bit_le(55));
    /// ```
    #[inline]
    fn test_bit_le(&self, index: u32) -> bool {
        self.test_bit_in::<LittleEndian>(index)
    }

    /// Test if the given bit is set using [`BigEndian`] indexing.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: u32 = bittle::set_be![];
    /// assert!(!a.test_bit_be(32));
    ///
    /// let a: u32 = bittle::set_be![32];
    /// assert!(a.test_bit_be(32));
    /// ```
    ///
    /// Using a larger set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u32; 2] = bittle::set_be![];
    /// assert!(!a.test_bit_be(55));
    ///
    /// let a: [u32; 2] = bittle::set_be![55];
    /// assert!(a.test_bit_be(55));
    /// ```
    #[inline]
    fn test_bit_be(&self, index: u32) -> bool {
        self.test_bit_in::<BigEndian>(index)
    }

    /// Construct an iterator over ones in the bit set using [`DefaultEndian`]
    /// indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
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
    /// let set: [u32; 4] = bittle::set![4, 67, 71, 127];
    /// assert!(set.iter_ones().eq([4, 67, 71, 127]));
    /// assert!(set.iter_ones().rev().eq([127, 71, 67, 4]));
    /// ```
    fn iter_ones(&self) -> Self::IterOnes<'_>;

    /// Construct an iterator over ones in the bit set.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let set: u128 = bittle::set_le![3, 7];
    /// assert!(set.iter_ones_in::<LittleEndian>().eq([3, 7]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let set: [u32; 4] = bittle::set_le![4, 67, 71];
    /// assert!(set.iter_ones_in::<LittleEndian>().eq([4, 67, 71]));
    /// ```
    fn iter_ones_in<E>(&self) -> Self::IterOnesIn<'_, E>
    where
        E: Endian;

    /// Construct an iterator over ones in the bit set using [`LittleEndian`]
    /// indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: u128 = bittle::set_le![3, 7];
    /// assert!(set.iter_ones_le().eq([3, 7]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: [u32; 4] = bittle::set_le![4, 67, 71];
    /// assert!(set.iter_ones_le().eq([4, 67, 71]));
    /// ```
    #[inline]
    fn iter_ones_le(&self) -> Self::IterOnesIn<'_, LittleEndian> {
        self.iter_ones_in()
    }

    /// Construct an iterator over ones in the bit set using [`BigEndian`]
    /// indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: u128 = bittle::set_be![3, 7];
    /// assert!(set.iter_ones_be().eq([3, 7]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: [u32; 4] = bittle::set_be![4, 67, 71];
    /// assert!(set.iter_ones_be().eq([4, 67, 71]));
    /// ```
    #[inline]
    fn iter_ones_be(&self) -> Self::IterOnesIn<'_, BigEndian> {
        self.iter_ones_in()
    }

    /// Construct an iterator over zeros in the bit set using [`DefaultEndian`]
    /// indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: u8 = bittle::set![3, 7];
    /// assert!(set.iter_zeros().eq([0, 1, 2, 4, 5, 6]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: [u8; 2] = bittle::set![3, 7, 13, 14, 15];
    /// assert!(set.iter_zeros().eq([0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 12]));
    /// assert!(set.iter_zeros().rev().eq([12, 11, 10, 9, 8, 6, 5, 4, 2, 1, 0]));
    /// ```
    fn iter_zeros(&self) -> Self::IterZeros<'_>;

    /// Construct an iterator over zeros in the bit set.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let set: u8 = bittle::set_le![3, 7];
    /// assert!(set.iter_zeros_in::<LittleEndian>().eq([0, 1, 2, 4, 5, 6]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let set: [u8; 2] = bittle::set_le![3, 7, 13, 14, 15];
    /// assert!(set.iter_zeros_in::<LittleEndian>().eq([0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 12]));
    /// ```
    fn iter_zeros_in<E>(&self) -> Self::IterZerosIn<'_, E>
    where
        E: Endian;

    /// Construct an iterator over zeros in the bit set using [`LittleEndian`] indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: u8 = bittle::set_le![3, 7];
    /// assert!(set.iter_zeros_le().eq([0, 1, 2, 4, 5, 6]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: [u8; 2] = bittle::set_le![3, 7, 13, 14, 15];
    /// assert!(set.iter_zeros_le().eq([0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 12]));
    /// ```
    #[inline]
    fn iter_zeros_le(&self) -> Self::IterZerosIn<'_, LittleEndian> {
        self.iter_zeros_in()
    }

    /// Construct an iterator over zeros in the bit set using [`BigEndian`]
    /// indexing.
    ///
    /// Will iterate through elements from smallest to largest index.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: u8 = bittle::set_be![3, 7];
    /// assert!(set.iter_zeros_be().eq([0, 1, 2, 4, 5, 6]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: [u8; 2] = bittle::set_be![3, 7, 13, 14, 15];
    /// assert!(set.iter_zeros_be().eq([0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 12]));
    /// ```
    #[inline]
    fn iter_zeros_be(&self) -> Self::IterZerosIn<'_, BigEndian> {
        self.iter_zeros_in()
    }

    /// Join this bit set with an iterator, creating an iterator that only
    /// yields the elements which are set to ones using custom [`Endian`]
    /// indexing.
    ///
    /// The underlying iterator is advanced using [`Iterator::nth`] as
    /// appropriate.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let mask: u128 = bittle::set_le![0, 1, 3];
    /// let mut values = vec![false, false, false, false];
    ///
    /// for value in mask.join_ones_in::<_, LittleEndian>(values.iter_mut()) {
    ///     *value = true;
    /// }
    ///
    /// assert_eq!(values, vec![true, true, false, true]);
    /// ```
    fn join_ones_in<I, E>(&self, iter: I) -> JoinOnes<'_, Self, E, I::IntoIter>
    where
        I: IntoIterator,
        E: Endian,
    {
        JoinOnes::new(self.iter_ones_in(), iter.into_iter())
    }

    /// Join this bit set with an iterator, creating an iterator that only
    /// yields the elements which are set to ones using [`DefaultEndian`]
    /// indexing.
    ///
    /// The underlying iterator is advanced using [`Iterator::nth`] as
    /// appropriate.
    ///
    /// [`DefaultEndian`]: crate::DefaultEndian
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
    #[inline]
    fn join_ones<I>(&self, iter: I) -> JoinOnes<'_, Self, DefaultEndian, I::IntoIter>
    where
        I: IntoIterator,
    {
        JoinOnes::new(self.iter_ones_in(), iter.into_iter())
    }

    /// Join this bit set with an iterator, creating an iterator that only
    /// yields the elements which are set to ones using [`LittleEndian`] indexing.
    ///
    /// The underlying iterator is advanced using [`Iterator::nth`] as
    /// appropriate.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mask: u8 = 0b11010000;
    /// let mut values = vec![false, false, false, false];
    ///
    /// for value in mask.join_ones_le(values.iter_mut()) {
    ///     *value = true;
    /// }
    ///
    /// assert_eq!(values, vec![true, true, false, true]);
    /// ```
    #[inline]
    fn join_ones_le<I>(&self, iter: I) -> JoinOnes<'_, Self, LittleEndian, I::IntoIter>
    where
        I: IntoIterator,
    {
        self.join_ones_in(iter)
    }

    /// Join this bit set with an iterator, creating an iterator that only
    /// yields the elements which are set to ones using [`BigEndian`] indexing.
    ///
    /// The underlying iterator is advanced using [`Iterator::nth`] as
    /// appropriate.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mask: u8 = 0b00001011;
    /// let mut values = vec![false, false, false, false];
    ///
    /// for value in mask.join_ones_be(values.iter_mut()) {
    ///     *value = true;
    /// }
    ///
    /// assert_eq!(values, vec![true, true, false, true]);
    /// ```
    #[inline]
    fn join_ones_be<I>(&self, iter: I) -> JoinOnes<'_, Self, BigEndian, I::IntoIter>
    where
        I: IntoIterator,
    {
        self.join_ones_in(iter)
    }
}

impl<T> Bits for &T
where
    T: ?Sized + Bits,
{
    type IterOnes<'a>
        = T::IterOnes<'a>
    where
        Self: 'a;

    type IterOnesIn<'a, E>
        = T::IterOnesIn<'a, E>
    where
        Self: 'a,
        E: Endian;

    type IterZeros<'a>
        = T::IterZeros<'a>
    where
        Self: 'a;

    type IterZerosIn<'a, E>
        = T::IterZerosIn<'a, E>
    where
        Self: 'a,
        E: Endian;

    #[inline]
    fn count_ones(&self) -> u32 {
        (**self).count_ones()
    }

    #[inline]
    fn count_zeros(&self) -> u32 {
        (**self).count_zeros()
    }

    #[inline]
    fn bits_capacity(&self) -> u32 {
        (**self).bits_capacity()
    }

    #[inline]
    fn all_zeros(&self) -> bool {
        (**self).all_zeros()
    }

    #[inline]
    fn all_ones(&self) -> bool {
        (**self).all_ones()
    }

    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        (**self).test_bit(index)
    }

    #[inline]
    fn test_bit_in<E>(&self, index: u32) -> bool
    where
        E: Endian,
    {
        (**self).test_bit_in::<E>(index)
    }

    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        (**self).iter_ones()
    }

    #[inline]
    fn iter_ones_in<E>(&self) -> Self::IterOnesIn<'_, E>
    where
        E: Endian,
    {
        (**self).iter_ones_in()
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        (**self).iter_zeros()
    }

    #[inline]
    fn iter_zeros_in<E>(&self) -> Self::IterZerosIn<'_, E>
    where
        E: Endian,
    {
        (**self).iter_zeros_in()
    }
}

impl<T> Bits for &mut T
where
    T: ?Sized + Bits,
{
    type IterOnesIn<'a, E>
        = T::IterOnesIn<'a, E>
    where
        Self: 'a,
        E: Endian;

    type IterOnes<'a>
        = T::IterOnes<'a>
    where
        Self: 'a;

    type IterZerosIn<'a, E>
        = T::IterZerosIn<'a, E>
    where
        Self: 'a,
        E: Endian;

    type IterZeros<'a>
        = T::IterZeros<'a>
    where
        Self: 'a;

    #[inline]
    fn count_ones(&self) -> u32 {
        (**self).count_ones()
    }

    #[inline]
    fn count_zeros(&self) -> u32 {
        (**self).count_zeros()
    }

    #[inline]
    fn bits_capacity(&self) -> u32 {
        (**self).bits_capacity()
    }

    #[inline]
    fn all_zeros(&self) -> bool {
        (**self).all_zeros()
    }

    #[inline]
    fn all_ones(&self) -> bool {
        (**self).all_ones()
    }

    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        (**self).test_bit(index)
    }

    #[inline]
    fn test_bit_in<E>(&self, index: u32) -> bool
    where
        E: Endian,
    {
        (**self).test_bit_in::<E>(index)
    }

    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        (**self).iter_ones()
    }

    #[inline]
    fn iter_ones_in<E>(&self) -> Self::IterOnesIn<'_, E>
    where
        E: Endian,
    {
        (**self).iter_ones_in()
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        (**self).iter_zeros()
    }

    #[inline]
    fn iter_zeros_in<E>(&self) -> Self::IterZerosIn<'_, E>
    where
        E: Endian,
    {
        (**self).iter_zeros_in()
    }
}
