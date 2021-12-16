//! A fixed size bit set.

use crate::mask::Mask;
use std::cmp;
use std::fmt;
use std::hash::{Hash, Hasher};

/// A fixed size bit set.
///
/// # Examples
///
/// ```
/// use bittle::FixedSet;
///
/// let mut set = FixedSet::<u128>::empty();
///
/// assert!(!set.test(1));
/// set.set(1);
/// assert!(set.test(1));
/// set.unset(1);
/// assert!(!set.test(1));
/// ```
///
/// The bit set can also use arrays as its backing storage.
///
/// ```
/// use bittle::FixedSet;
///
/// let mut set = FixedSet::<[u64; 16]>::empty();
///
/// assert!(!set.test(172));
/// set.set(172);
/// assert!(set.test(172));
/// set.unset(172);
/// assert!(!set.test(172));
/// ```
///
/// We can use the iterator of each set to compare bit sets of different kinds:
///
/// ```
/// use bittle::FixedSet;
///
/// let mut a = FixedSet::<[u64; 2]>::empty();
/// let mut b = FixedSet::<u128>::empty();
///
/// a.set(111);
/// assert!(!a.iter().eq(b.iter()));
///
/// b.set(111);
/// assert!(a.iter().eq(b.iter()));
/// ```
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct FixedSet<T>
where
    T: Bits,
{
    bits: T,
}

impl<T> FixedSet<T>
where
    T: Bits,
{
    /// Construct a bit set from an array.
    pub fn from_array<const N: usize>(items: [usize; N]) -> Self {
        let mut set = Self::empty();

        for n in items {
            set.set(n);
        }

        set
    }

    /// Test if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::empty();
    /// assert!(set.is_empty());
    /// set.set(4);
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.bits == T::EMPTY
    }

    /// Test if this set is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::full();
    /// assert!(set.is_full());
    /// set.unset(4);
    /// assert!(!set.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        self.bits == T::FULL
    }

    /// Construct a new bit set that is empty, where no element is set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let set = FixedSet::<u128>::empty();
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), vec![])
    /// ```
    pub fn empty() -> Self {
        Self { bits: T::EMPTY }
    }

    /// Construct a new bit set that is full, where every single element
    /// possible is set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let set = FixedSet::<u128>::full();
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), (0..128usize).collect::<Vec<_>>())
    /// ```
    pub fn full() -> Self {
        Self { bits: T::FULL }
    }

    /// Test if the given bit is set.
    ///
    /// Elements which are out of bounds of the bit set will always return
    /// `false`.
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u8>::full();
    /// assert!(!set.test(1024));
    ///
    /// let mut set = FixedSet::<[u8; 24]>::full();
    /// assert!(!set.test(1024));
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::full();
    ///
    /// assert!(set.test(0));
    /// assert!(set.test(1));
    /// assert!(set.test(127));
    ///
    /// set.unset(1);
    ///
    /// assert!(set.test(0));
    /// assert!(!set.test(1));
    /// assert!(set.test(127));
    /// ```
    pub fn test(&self, index: usize) -> bool {
        self.bits.test(index)
    }

    /// Set the given bit.
    ///
    /// Setting a bit which is out of bounds does nothing.
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u8>::empty();
    /// set.set(1024);
    /// assert!(set.is_empty());
    ///
    /// let mut set = FixedSet::<[u8; 24]>::empty();
    /// set.set(1024);
    /// assert!(set.is_empty());
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::full();
    ///
    /// assert!(set.test(0));
    /// assert!(set.test(1));
    /// assert!(set.test(127));
    ///
    /// set.unset(1);
    ///
    /// assert!(set.test(0));
    /// assert!(!set.test(1));
    /// assert!(set.test(127));
    ///
    /// set.set(1);
    ///
    /// assert!(set.test(0));
    /// assert!(set.test(1));
    /// assert!(set.test(127));
    /// ```
    pub fn set(&mut self, index: usize) {
        self.bits.set(index);
    }

    /// Unset the given bit.
    ///
    /// Unsetting a bit which is out of bounds does nothing.
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u8>::full();
    /// set.unset(1024);
    /// assert!(set.is_full());
    ///
    /// let mut set = FixedSet::<[u8; 24]>::full();
    /// set.unset(1024);
    /// assert!(set.is_full());
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::full();
    ///
    /// assert!(set.test(0));
    /// assert!(set.test(1));
    /// assert!(set.test(127));
    ///
    /// set.unset(1);
    ///
    /// assert!(set.test(0));
    /// assert!(!set.test(1));
    /// assert!(set.test(127));
    ///
    /// set.set(1);
    ///
    /// assert!(set.test(0));
    /// assert!(set.test(1));
    /// assert!(set.test(127));
    /// ```
    pub fn unset(&mut self, index: usize) {
        self.bits.unset(index);
    }

    /// Clear the entire bit pattern.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::full();
    ///
    /// assert!(set.test(0));
    /// assert!(set.test(1));
    /// assert!(set.test(127));
    ///
    /// set.clear();
    ///
    /// assert!(!set.test(0));
    /// assert!(!set.test(1));
    /// assert!(!set.test(127));
    ///
    /// set.set(1);
    ///
    /// assert!(!set.test(0));
    /// assert!(set.test(1));
    /// assert!(!set.test(127));
    /// ```
    pub fn clear(&mut self) {
        self.bits.clear();
    }

    /// Merge this set with another.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut a = FixedSet::<u128>::empty();
    /// a.set(31);
    /// a.set(67);
    ///
    /// let mut b = FixedSet::<u128>::empty();
    /// b.set(62);
    ///
    /// b.merge(&a);
    ///
    /// assert!(b.test(31));
    /// assert!(b.test(62));
    /// assert!(b.test(67));
    /// ```
    pub fn merge(&mut self, other: &Self) {
        self.bits.merge(&other.bits);
    }

    /// Construct an iterator over a bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::empty();
    ///
    /// set.set(3);
    /// set.set(7);
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), vec![3, 7]);
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::{FixedSet, Mask};
    ///
    /// let mut set = FixedSet::<[u32; 4]>::empty();
    ///
    /// set.set(4);
    /// set.set(63);
    /// set.set(71);
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), vec![4, 63, 71]);
    /// ```
    pub fn iter(&self) -> T::Iter {
        self.bits.iter()
    }
}

impl<T> fmt::Debug for FixedSet<T>
where
    T: Bits,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> cmp::PartialEq for FixedSet<T>
where
    T: Bits,
{
    fn eq(&self, other: &Self) -> bool {
        self.bits.eq(&other.bits)
    }
}

impl<T> cmp::Eq for FixedSet<T> where T: Bits {}

impl<T> cmp::PartialOrd for FixedSet<T>
where
    T: Bits,
{
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.bits.partial_cmp(&other.bits)
    }
}

impl<T> cmp::Ord for FixedSet<T>
where
    T: Bits,
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.bits.cmp(&other.bits)
    }
}

impl<T> Hash for FixedSet<T>
where
    T: Bits,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bits.hash(state);
    }
}

impl<T> IntoIterator for FixedSet<T>
where
    T: Bits,
{
    type IntoIter = T::Iter;
    type Item = <Self::IntoIter as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over a bit bits. Created through [FixedSet::iter].
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Iter<T>
where
    T: Bits + Number,
{
    bits: T,
}

impl<T> Iterator for Iter<T>
where
    T: Bits + Number,
{
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.bits == T::EMPTY {
            return None;
        }

        let index = self.bits.trailing_zeros();
        self.bits.unset(index);
        Some(index)
    }
}

/// An iterator over a bit bits. Created through [FixedSet::iter].
#[derive(Clone, Copy)]
pub struct ArrayIter<T, const N: usize>
where
    T: Bits + Number,
{
    bits: [T; N],
    o: usize,
}

impl<T, const N: usize> Iterator for ArrayIter<T, N>
where
    T: Bits + Number,
{
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bits) = self.bits.get_mut(self.o) {
            if *bits != T::EMPTY {
                let index = bits.trailing_zeros();
                bits.unset(index);
                return Some(self.o * T::BITS + index);
            }

            self.o += 1;
        }

        None
    }
}

/// Basic numerical trait for the plumbing of a bit set. This ensures that only
/// primitive types can be used as the basis of a bit set backed by an array,
/// like `[u64; 4]` and not `[[u32; 2]; 4]`.
pub trait Number: Bits {
    /// How many bits there are in this number.
    const BITS: usize = std::mem::size_of::<Self>() * 8;

    /// Number of trailing zeros.
    fn trailing_zeros(self) -> usize;
}

/// The trait for a bit pattern.
pub trait Bits: Sized + Copy + Eq + Ord + Hash {
    /// The iterator over this bit pattern.
    ///
    /// See [FixedSet::iter].
    type Iter: Iterator<Item = usize>;

    /// Bit-pattern for an empty bit pattern.
    ///
    /// See [FixedSet::empty].
    const EMPTY: Self;

    /// Bit-pattern for a full bit pattern.
    ///
    /// See [FixedSet::full].
    const FULL: Self;

    /// Test if the given bit is set.
    ///
    /// See [FixedSet::test].
    fn test(&self, index: usize) -> bool;

    /// Set the given bit in the bit pattern.
    ///
    /// See [FixedSet::set].
    fn set(&mut self, index: usize);

    /// Unset the given bit in the bit pattern.
    ///
    /// See [FixedSet::unset].
    fn unset(&mut self, index: usize);

    /// Clear the entire bit pattern.
    ///
    /// See [FixedSet::clear].
    fn clear(&mut self);

    /// Merge these bits with another.
    ///
    /// See [FixedSet::merge].
    fn merge(&mut self, other: &Self);

    /// Construct an iterator over a bit pattern.
    ///
    /// See [FixedSet::iter].
    fn iter(self) -> Self::Iter;
}

macro_rules! impl_num_bits {
    ($ty:ty) => {
        impl Number for $ty {
            fn trailing_zeros(self) -> usize {
                <Self>::trailing_zeros(self) as usize
            }
        }

        impl Bits for $ty {
            type Iter = Iter<Self>;

            const EMPTY: Self = 0;
            const FULL: Self = !0;

            #[inline]
            fn test(&self, index: usize) -> bool {
                if index > <$ty>::BITS as usize {
                    return false;
                }

                (*self & (1 << index)) != 0
            }

            #[inline]
            fn set(&mut self, index: usize) {
                if index <= <$ty>::BITS as usize {
                    *self |= 1 << index;
                }
            }

            #[inline]
            fn merge(&mut self, other: &Self) {
                *self ^= other;
            }

            #[inline]
            fn unset(&mut self, index: usize) {
                if index <= <$ty>::BITS as usize {
                    *self &= !(1 << index);
                }
            }

            #[inline]
            fn clear(&mut self) {
                *self = Self::EMPTY;
            }

            #[inline]
            fn iter(self) -> Self::Iter {
                Iter { bits: self }
            }
        }
    };
}

impl_num_bits!(u128);
impl_num_bits!(u64);
impl_num_bits!(u32);
impl_num_bits!(u16);
impl_num_bits!(u8);

impl<T, const N: usize> Bits for [T; N]
where
    T: Bits + Number,
{
    type Iter = ArrayIter<T, N>;

    const EMPTY: Self = [T::EMPTY; N];
    const FULL: Self = [T::FULL; N];

    fn test(&self, index: usize) -> bool {
        if let Some(bits) = self.get(index / T::BITS) {
            return bits.test(index % T::BITS);
        }

        false
    }

    fn set(&mut self, index: usize) {
        if let Some(bits) = self.get_mut(index / T::BITS) {
            bits.set(index % T::BITS);
        }
    }

    fn merge(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.merge(i);
        }
    }

    fn unset(&mut self, index: usize) {
        if let Some(bits) = self.get_mut(index / T::BITS) {
            bits.unset(index % T::BITS);
        }
    }

    fn clear(&mut self) {
        for b in self {
            b.clear();
        }
    }

    fn iter(self) -> Self::Iter {
        ArrayIter { bits: self, o: 0 }
    }
}

impl<T> Mask for FixedSet<T>
where
    T: Bits,
{
    type Iter = T::Iter;

    #[inline]
    fn test(&self, index: usize) -> bool {
        <FixedSet<T>>::test(self, index)
    }

    #[inline]
    fn iter(&self) -> Self::Iter {
        <FixedSet<T>>::iter(self)
    }
}
