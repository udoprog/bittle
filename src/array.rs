//! [Bits] associated types for primitive arrays.

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::endian::{DefaultEndian, Endian};
use crate::slice::{IterOnes, IterZeros};

impl<T, const N: usize> BitsOwned for [T; N]
where
    T: Eq + BitsOwned,
{
    #[allow(clippy::cast_possible_truncation)]
    const BITS: u32 = match T::BITS.checked_mul(N as u32) {
        Some(value) => value,
        None => panic!("32-bit overflow in capacity"),
    };
    const ZEROS: Self = [T::ZEROS; N];
    const ONES: Self = [T::ONES; N];

    type IntoIterOnes = IntoIterOnes<T, N, DefaultEndian>;
    type IntoIterOnesIn<E>
        = IntoIterOnes<T, N, E>
    where
        E: Endian;
    type IntoIterZeros = IntoIterZeros<T, N, DefaultEndian>;
    type IntoIterZerosIn<E>
        = IntoIterZeros<T, N, E>
    where
        E: Endian;

    #[inline]
    fn zeros() -> Self {
        Self::ZEROS
    }

    #[inline]
    fn ones() -> Self {
        Self::ONES
    }

    #[inline]
    fn with_bit_in<E>(mut self, bit: u32) -> Self
    where
        E: Endian,
    {
        self[(bit / T::BITS) as usize % N].set_bit_in::<E>(bit % T::BITS);
        self
    }

    #[inline]
    fn with_bit(self, bit: u32) -> Self {
        self.with_bit_in::<DefaultEndian>(bit)
    }

    #[inline]
    fn without_bit_in<E>(mut self, bit: u32) -> Self
    where
        E: Endian,
    {
        self[(bit / T::BITS) as usize % N].clear_bit_in::<E>(bit % T::BITS);
        self
    }

    #[inline]
    fn without_bit(self, bit: u32) -> Self {
        self.without_bit_in::<DefaultEndian>(bit)
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
        IntoIterOnes::new(self)
    }

    #[inline]
    fn into_iter_ones_in<E>(self) -> Self::IntoIterOnesIn<E>
    where
        E: Endian,
    {
        IntoIterOnes::new(self)
    }

    #[inline]
    fn into_iter_zeros(self) -> Self::IntoIterZeros {
        IntoIterZeros::new(self)
    }

    #[inline]
    fn into_iter_zeros_in<E>(self) -> Self::IntoIterZerosIn<E>
    where
        E: Endian,
    {
        IntoIterZeros::new(self)
    }
}

impl<T, const N: usize> Bits for [T; N]
where
    T: Eq + BitsOwned,
{
    type IterOnes<'a>
        = IterOnes<'a, T, DefaultEndian>
    where
        Self: 'a;
    type IterOnesIn<'a, E>
        = IterOnes<'a, T, E>
    where
        Self: 'a,
        E: Endian;
    type IterZeros<'a>
        = IterZeros<'a, T, DefaultEndian>
    where
        Self: 'a;
    type IterZerosIn<'a, E>
        = IterZeros<'a, T, E>
    where
        Self: 'a,
        E: Endian;

    /// Count the number of ones in the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// assert_eq!(a.count_ones(), 3);
    /// ```
    #[inline]
    fn count_ones(&self) -> u32 {
        self.iter().map(Bits::count_ones).sum()
    }

    /// Count the number of zeros in the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// assert_eq!(a.count_zeros(), 13);
    /// ```
    #[inline]
    fn count_zeros(&self) -> u32 {
        self.iter().map(Bits::count_zeros).sum()
    }

    /// Get the capacity of the array.
    ///
    /// The capacity of a array is determined by its length.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u8; 4] = bittle::set![4, 11, 14];
    /// assert_eq!(a.bits_capacity(), 32);
    /// ```
    ///
    /// Also note that the capacity of an array is known at compile-time through
    /// [`BitsOwned::BITS`]:
    ///
    /// ```
    /// use bittle::BitsOwned;
    ///
    /// const CAP: u32 = <[u8; 4]>::BITS;
    /// assert_eq!(CAP, 32);
    /// ```
    #[inline]
    fn bits_capacity(&self) -> u32 {
        Self::BITS
    }

    /// Test if the array is all zeros.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u8; 2] = bittle::set![];
    /// assert!(a.all_zeros());
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// assert!(!a.all_zeros());
    /// ```
    #[inline]
    fn all_zeros(&self) -> bool {
        *self == Self::ZEROS
    }

    /// Test if the array is all ones.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u8; 2] = bittle::set![0..16];
    /// assert!(a.all_ones());
    ///
    /// let a: [u8; 2] = bittle::set![4, 11, 14];
    /// assert!(!a.all_ones());
    /// ```
    #[inline]
    fn all_ones(&self) -> bool {
        *self == Self::ONES
    }

    /// Test if the given bit is set in the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u8; 2] = bittle::set![4, 11, 14];
    /// assert!(a.test_bit(4));
    /// ```
    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        self.test_bit_in::<DefaultEndian>(index)
    }

    /// Test if the given bit is set in the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BigEndian};
    ///
    /// let mut a: [u8; 2] = bittle::set_be![4, 11, 14];
    /// assert!(a.test_bit_in::<BigEndian>(4));
    /// ```
    #[inline]
    fn test_bit_in<E>(&self, index: u32) -> bool
    where
        E: Endian,
    {
        self[(index / T::BITS) as usize % N].test_bit_in::<E>(index % T::BITS)
    }

    /// Iterates over all ones in the array using [`DefaultEndian`] indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u8; 2] = bittle::set![4, 11, 14];
    /// assert!(a.iter_ones().eq([4, 11, 14]));
    ///
    /// let a: [u8; 0] = [];
    /// assert!(a.iter_ones().eq([]));
    /// ```
    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        IterOnes::new(self)
    }

    /// Iterates over all ones in the array using a custom [`Endian`] indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let mut a: [u8; 2] = bittle::set_le![4, 11, 14];
    /// assert!(a.iter_ones_in::<LittleEndian>().eq([4, 11, 14]));
    /// ```
    #[inline]
    fn iter_ones_in<E>(&self) -> Self::IterOnesIn<'_, E>
    where
        E: Endian,
    {
        IterOnes::new(self)
    }

    /// Iterates over all zeros in the array using [`DefaultEndian`] indexing.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u8; 2] = bittle::set![4, 11, 14];
    /// assert!(a.iter_zeros().eq([0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 15]));
    ///
    /// let a: [u8; 0] = [];
    /// assert!(a.iter_zeros().eq([]));
    /// ```
    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        IterZeros::new(self)
    }

    /// Iterates over all zeros in the array using a custom [`Endian`] indexing
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, LittleEndian};
    ///
    /// let mut a: [u8; 2] = bittle::set_le![4, 11, 14];
    /// assert!(a.iter_zeros_in::<LittleEndian>().eq([0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 15]));
    /// ```
    #[inline]
    fn iter_zeros_in<E>(&self) -> Self::IterZerosIn<'_, E>
    where
        E: Endian,
    {
        IterZeros::new(self)
    }
}

impl<T, const N: usize> BitsMut for [T; N]
where
    T: Eq + BitsOwned,
{
    #[inline]
    fn set_bit_in<E>(&mut self, index: u32)
    where
        E: Endian,
    {
        self[(index / T::BITS) as usize % N].set_bit_in::<E>(index % T::BITS);
    }

    #[inline]
    fn set_bit(&mut self, index: u32) {
        self.set_bit_in::<DefaultEndian>(index);
    }

    #[inline]
    fn clear_bit_in<E>(&mut self, index: u32)
    where
        E: Endian,
    {
        self[(index / T::BITS) as usize % N].clear_bit_in::<E>(index % T::BITS);
    }

    #[inline]
    fn clear_bit(&mut self, index: u32) {
        self.clear_bit_in::<DefaultEndian>(index);
    }

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

impl_iter! {
    /// An owned iterator over the bits set to one in an array.
    {T, const N: usize, E} IntoIterOnes<T, N, E>
    {into_iter_ones_in, T::IntoIterOnesIn<E>, core::array::IntoIter<T, N>}
    {array: [T; N] => N}
    {T: Clone}
}

impl_iter! {
    /// An owned iterator over the bits set to zero in an array.
    {T, const N: usize, E} IntoIterZeros<T, N, E>
    {into_iter_zeros_in, T::IntoIterZerosIn<E>, core::array::IntoIter<T, N>}
    {array: [T; N] => N}
    {T: Clone}
}
