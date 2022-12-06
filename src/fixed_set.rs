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
/// let mut set = FixedSet::<u128>::new();
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
/// let mut set = FixedSet::<[u64; 16]>::new();
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
/// let mut a = FixedSet::<[u64; 2]>::new();
/// let mut b = FixedSet::<u128>::new();
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
    /// Construct a new bit set that is empty, where no element is set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let set = FixedSet::<u128>::new();
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), vec![])
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self { bits: T::EMPTY }
    }

    /// Construct a set from its underlying bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u8>::from_bits(0b00001001);
    ///
    /// assert!(!set.is_empty());
    /// assert!(set.test(0));
    /// assert!(!set.test(1));
    /// assert!(!set.test(2));
    /// assert!(set.test(3));
    /// ```
    #[inline]
    pub const fn from_bits(bits: T) -> Self {
        Self { bits }
    }

    /// Construct a bitset from a collection of indexes.
    #[inline]
    pub fn from_indexes<const N: usize>(items: [u32; N]) -> Self {
        let mut set = Self::new();

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
    /// let mut set = FixedSet::<u128>::new();
    /// assert!(set.is_empty());
    /// set.set(4);
    /// assert!(!set.is_empty());
    /// ```
    #[inline]
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
    #[inline]
    pub fn is_full(&self) -> bool {
        self.bits == T::FULL
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
    /// assert_eq!(set.iter().collect::<Vec<_>>(), (0..128u32).collect::<Vec<_>>())
    /// ```
    #[inline]
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
    #[inline]
    pub fn test(&self, index: u32) -> bool {
        self.bits.test(index)
    }

    /// Set the given bit.
    ///
    /// Setting a bit which is out of bounds does nothing.
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u8>::new();
    /// set.set(1024);
    /// assert!(set.is_empty());
    ///
    /// let mut set = FixedSet::<[u8; 24]>::new();
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
    #[inline]
    pub fn set(&mut self, index: u32) {
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
    #[inline]
    pub fn unset(&mut self, index: u32) {
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
    #[inline]
    pub fn clear(&mut self) {
        self.bits.clear();
    }

    /// Construct the union between this and another set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut a = FixedSet::<u128>::new();
    /// a.set(31);
    /// a.set(67);
    ///
    /// let mut b = FixedSet::<u128>::new();
    /// b.set(31);
    /// b.set(62);
    ///
    /// a.union(&b);
    ///
    /// assert!(a.test(31));
    /// assert!(a.test(62));
    /// assert!(a.test(67));
    /// ```
    #[inline]
    pub fn union(&mut self, other: &Self) {
        self.bits.union(&other.bits);
    }

    /// Construct the difference between this and another set.
    ///
    /// The new set will contain elements which are exlusively contained in the
    /// second set. This is not a commutative operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut a = FixedSet::<u128>::new();
    /// a.set(31);
    /// a.set(67);
    ///
    /// let mut b = FixedSet::<u128>::new();
    /// b.set(31);
    /// b.set(62);
    ///
    /// let mut c = a;
    /// c.difference(&b);
    ///
    /// let mut d = b;
    /// d.difference(&a);
    ///
    /// assert_ne!(c, d);
    ///
    /// assert!(!c.test(31));
    /// assert!(c.test(62));
    /// assert!(!c.test(67));
    ///
    /// assert!(!d.test(31));
    /// assert!(!d.test(62));
    /// assert!(d.test(67));
    /// ```
    #[inline]
    pub fn difference(&mut self, other: &Self) {
        self.bits.difference(&other.bits);
    }

    /// Construct the symmetric difference between this and another set.
    ///
    /// The new set will contain elements which exist exclusively in one or the
    /// other.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut a = FixedSet::<u128>::new();
    /// a.set(31);
    /// a.set(67);
    ///
    /// let mut b = FixedSet::<u128>::new();
    /// b.set(31);
    /// b.set(62);
    ///
    /// let mut c = a;
    /// c.symmetric_difference(&b);
    ///
    /// assert!(!c.test(31));
    /// assert!(c.test(62));
    /// assert!(c.test(67));
    /// ```
    #[inline]
    pub fn symmetric_difference(&mut self, other: &Self) {
        self.bits.symmetric_difference(&other.bits);
    }

    /// Construct an iterator over a bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::FixedSet;
    ///
    /// let mut set = FixedSet::<u128>::new();
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
    /// let mut set = FixedSet::<[u32; 4]>::new();
    ///
    /// set.set(4);
    /// set.set(63);
    /// set.set(71);
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), vec![4, 63, 71]);
    /// ```
    #[inline]
    pub fn iter(&self) -> T::Iter {
        self.bits.iter()
    }
}

impl<T> FixedSet<T>
where
    T: Number,
{
    /// Perform a fast length calculation for bitsets specialized over numerical types.
    #[inline]
    pub fn len(&self) -> u32 {
        T::count_ones(self.bits)
    }
}

impl<T> fmt::Debug for FixedSet<T>
where
    T: Bits,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> cmp::PartialEq for FixedSet<T>
where
    T: Bits,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.bits.eq(&other.bits)
    }
}

impl<T> cmp::Eq for FixedSet<T> where T: Bits {}

impl<T> cmp::PartialOrd for FixedSet<T>
where
    T: Bits,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.bits.partial_cmp(&other.bits)
    }
}

impl<T> cmp::Ord for FixedSet<T>
where
    T: Bits,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.bits.cmp(&other.bits)
    }
}

impl<T> Hash for FixedSet<T>
where
    T: Bits,
{
    #[inline]
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

    #[inline]
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
    type Item = u32;

    #[inline]
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
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bits) = self.bits.get_mut(self.o) {
            if *bits != T::EMPTY {
                let index = bits.trailing_zeros();
                bits.unset(index);
                return Some(self.o as u32 * T::BITS + index);
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
    const BITS: u32 = (std::mem::size_of::<Self>() * 8) as u32;

    /// Number of trailing zeros.
    fn trailing_zeros(self) -> u32;

    /// Count number of ones.
    fn count_ones(self) -> u32;
}

/// The trait for a bit pattern.
pub trait Bits: Sized + Copy + Eq + Ord + Hash {
    /// The iterator over this bit pattern.
    ///
    /// See [FixedSet::iter].
    type Iter: Iterator<Item = u32>;

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
    fn test(&self, index: u32) -> bool;

    /// Set the given bit in the bit pattern.
    ///
    /// See [FixedSet::set].
    fn set(&mut self, index: u32);

    /// Unset the given bit in the bit pattern.
    ///
    /// See [FixedSet::unset].
    fn unset(&mut self, index: u32);

    /// Clear the entire bit pattern.
    ///
    /// See [FixedSet::clear].
    fn clear(&mut self);

    /// Construct the union between two sets of bits.
    ///
    /// See [FixedSet::union].
    fn union(&mut self, other: &Self);

    /// Construct the difference between two sets of bits.
    ///
    /// See [FixedSet::difference].
    fn difference(&mut self, other: &Self);

    /// Construct the symmetric difference between two sets of bits.
    ///
    /// See [FixedSet::symmetric_difference].
    fn symmetric_difference(&mut self, other: &Self);

    /// Construct an iterator over a bit pattern.
    ///
    /// See [FixedSet::iter].
    fn iter(self) -> Self::Iter;
}

macro_rules! impl_num_bits {
    ($ty:ty) => {
        impl Number for $ty {
            #[inline]
            fn trailing_zeros(self) -> u32 {
                <Self>::trailing_zeros(self)
            }

            #[inline]
            fn count_ones(self) -> u32 {
                <Self>::count_ones(self)
            }
        }

        impl Bits for $ty {
            type Iter = Iter<Self>;

            const EMPTY: Self = 0;
            const FULL: Self = !0;

            #[inline]
            fn test(&self, index: u32) -> bool {
                if index > <$ty>::BITS {
                    return false;
                }

                (*self & (1 << index)) != 0
            }

            #[inline]
            fn set(&mut self, index: u32) {
                if index <= <$ty>::BITS {
                    *self |= 1 << index;
                }
            }

            #[inline]
            fn union(&mut self, other: &Self) {
                *self |= other;
            }

            #[inline]
            fn difference(&mut self, other: &Self) {
                *self = other & !*self;
            }

            #[inline]
            fn symmetric_difference(&mut self, other: &Self) {
                *self ^= other;
            }

            #[inline]
            fn unset(&mut self, index: u32) {
                if index <= <$ty>::BITS {
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

    #[inline]
    fn test(&self, index: u32) -> bool {
        if let Some(bits) = self.get((index / T::BITS) as usize) {
            return bits.test(index % T::BITS);
        }

        false
    }

    #[inline]
    fn set(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.set(index % T::BITS);
        }
    }

    #[inline]
    fn union(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.union(i);
        }
    }

    #[inline]
    fn difference(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.difference(i);
        }
    }

    #[inline]
    fn symmetric_difference(&mut self, other: &Self) {
        for (o, i) in self.iter_mut().zip(other) {
            o.symmetric_difference(i);
        }
    }

    #[inline]
    fn unset(&mut self, index: u32) {
        if let Some(bits) = self.get_mut((index / T::BITS) as usize) {
            bits.unset(index % T::BITS);
        }
    }

    #[inline]
    fn clear(&mut self) {
        for b in self {
            b.clear();
        }
    }

    #[inline]
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
    fn test(&self, index: u32) -> bool {
        <FixedSet<T>>::test(self, index)
    }

    #[inline]
    fn iter(&self) -> Self::Iter {
        <FixedSet<T>>::iter(self)
    }
}
