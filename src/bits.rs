//! Traits which define the behaviors of a bit set.

mod join_ones;
pub use self::join_ones::JoinOnes;

mod sealed {
    pub trait Sealed {}

    impl<T> Sealed for &mut T where T: ?Sized + crate::Bits {}
    impl<T> Sealed for &T where T: ?Sized + crate::Bits {}
    impl<T> Sealed for [T] {}
    impl<T, const N: usize> Sealed for [T; N] {}
    impl<T> Sealed for crate::set::Set<T> where T: ?Sized {}
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
    /// The iterator over ones in this bit pattern.
    ///
    /// See [`Bits::iter_ones`].
    type IterOnes<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    /// The iterator over zeros in this bit pattern.
    ///
    /// See [`Bits::iter_zeros`].
    type IterZeros<'a>: Iterator<Item = u32>
    where
        Self: 'a;

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
    /// With arrays:
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
    /// let a: u32 = bittle::set![];
    /// assert!(a.all_zeros());
    ///
    /// let a: u32 = bittle::set![1];
    /// assert!(!a.all_zeros());
    /// ```
    ///
    /// With arrays:
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

    /// Test if the given bit is set.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
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
    /// # Examples
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

    /// Construct an iterator over ones in the bit set.
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

    /// Construct an iterator over zeros in the bit set.
    ///
    /// Will iterate through elements from smallest to largest index.
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
    /// ```
    fn iter_zeros(&self) -> Self::IterZeros<'_>;

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
        JoinOnes::new(self.iter_ones(), iter.into_iter())
    }
}

impl<T> Bits for &T
where
    T: ?Sized + Bits,
{
    type IterOnes<'a> = T::IterOnes<'a>
    where
        Self: 'a;

    type IterZeros<'a> = T::IterZeros<'a>
    where
        Self: 'a;

    #[inline]
    fn count_ones(&self) -> u32 {
        (**self).count_ones()
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
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        (**self).iter_ones()
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        (**self).iter_zeros()
    }
}

impl<T> Bits for &mut T
where
    T: ?Sized + Bits,
{
    type IterOnes<'a> = T::IterOnes<'a>
    where
        Self: 'a;

    type IterZeros<'a> = T::IterZeros<'a>
    where
        Self: 'a;

    #[inline]
    fn count_ones(&self) -> u32 {
        (**self).count_ones()
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
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        (**self).iter_ones()
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        (**self).iter_zeros()
    }
}
