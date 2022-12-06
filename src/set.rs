use core::cmp;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};

use crate::bits::{Bits, OwnedBits};
use crate::number::Number;

/// A convenience wrapper around a [Bits] which itself implements [Bits] and
/// a number of useful traits.
///
/// One reason one might want to use this wrapper is to have a
/// [Debug][fmt::Debug] implementation which shows which bits are actually in
/// use:
///
/// ```
/// use bittle::{Bits, Set};
///
/// let set: u128 = bittle::set![1, 14];
/// assert_eq!(format!("{set:?}"), "16386");
///
/// let set: Set<u128> = bittle::set![1, 14];
/// assert_eq!(format!("{set:?}"), "{1, 14}");
/// ```
///
/// This also provides unambigious implementations of [IntoIterator], whereas
/// arrays provide one themselves while primitive numbers do not.
///
/// # Examples
///
/// ```
/// use bittle::{Bits, OwnedBits, Set};
///
/// let mut set = Set::<u128>::empty();
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
/// use bittle::{Bits, Set};
///
/// let mut set = Set::<[u64; 16]>::new();
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
/// use bittle::{Bits, OwnedBits, Set};
///
/// let mut a = Set::<[u64; 2]>::empty();
/// let mut b = Set::<u128>::empty();
///
/// a.set(111);
/// assert!(!a.iter_bits().eq(b.iter_bits()));
///
/// b.set(111);
/// assert!(a.iter_bits().eq(b.iter_bits()));
/// ```
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Set<T> {
    bits: T,
}

impl<T> Set<T> {
    /// Construct a set from its underlying bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, Set};
    ///
    /// let mut set = Set::from_bits(0b00001001u32);
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
}

impl<T> Set<T>
where
    T: OwnedBits,
{
    /// Construct a new empty set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, Set};
    ///
    /// let mut set = Set::<u32>::new();
    ///
    /// assert!(set.is_empty());
    /// set.set(0);
    /// assert!(!set.is_empty());
    /// ```
    pub const fn new() -> Self {
        Self { bits: T::EMPTY }
    }
}

impl<T> OwnedBits for Set<T>
where
    T: OwnedBits,
{
    const BITS: u32 = T::BITS;
    const FULL: Self = Self { bits: T::FULL };
    const EMPTY: Self = Self { bits: T::EMPTY };

    type IntoBits = T::IntoBits;

    #[inline]
    fn empty() -> Self {
        Self { bits: T::EMPTY }
    }

    #[inline]
    fn full() -> Self {
        Self { bits: T::FULL }
    }

    #[inline]
    fn with(self, bit: u32) -> Self {
        Self {
            bits: self.bits.with(bit),
        }
    }

    #[inline]
    fn union(self, other: Self) -> Self {
        Self {
            bits: self.bits.union(other.bits),
        }
    }

    #[inline]
    fn conjunction(self, other: Self) -> Self {
        Self {
            bits: self.bits.conjunction(other.bits),
        }
    }

    #[inline]
    fn difference(self, other: Self) -> Self {
        Self {
            bits: self.bits.difference(other.bits),
        }
    }

    #[inline]
    fn symmetric_difference(self, other: Self) -> Self {
        Self {
            bits: self.bits.symmetric_difference(other.bits),
        }
    }

    #[inline]
    fn into_bits(self) -> T::IntoBits {
        self.bits.into_bits()
    }
}

impl<T> Bits for Set<T>
where
    T: Bits,
{
    type IterBits<'a> = T::IterBits<'a>
        where
            Self: 'a;

    #[inline]
    fn len(&self) -> u32 {
        self.bits.len()
    }

    #[inline]
    fn capacity(&self) -> u32 {
        self.bits.capacity()
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.bits.is_full()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.bits.is_empty()
    }

    #[inline]
    fn test(&self, index: u32) -> bool {
        self.bits.test(index)
    }

    #[inline]
    fn set(&mut self, index: u32) {
        self.bits.set(index);
    }

    #[inline]
    fn unset(&mut self, index: u32) {
        self.bits.unset(index);
    }

    #[inline]
    fn clear(&mut self) {
        self.bits.clear();
    }

    #[inline]
    fn union_assign(&mut self, other: &Self) {
        self.bits.union_assign(&other.bits);
    }

    #[inline]
    fn conjunction_assign(&mut self, other: &Self) {
        self.bits.conjunction_assign(&other.bits);
    }

    #[inline]
    fn difference_assign(&mut self, other: &Self) {
        self.bits.difference_assign(&other.bits);
    }

    #[inline]
    fn symmetric_difference_assign(&mut self, other: &Self) {
        self.bits.symmetric_difference_assign(&other.bits);
    }

    #[inline]
    fn iter_bits(&self) -> T::IterBits<'_> {
        self.bits.iter_bits()
    }
}

impl<T> Set<T>
where
    T: Number,
{
    /// Perform a fast length calculation for Bitss specialized over numerical types.
    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> u32 {
        T::count_ones(self.bits)
    }
}

impl<T> fmt::Debug for Set<T>
where
    T: OwnedBits,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter_bits()).finish()
    }
}

impl<T> cmp::PartialEq for Set<T>
where
    T: cmp::PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.bits.eq(&other.bits)
    }
}

impl<T> cmp::Eq for Set<T> where T: cmp::Eq {}

impl<T> cmp::PartialOrd for Set<T>
where
    T: cmp::PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.bits.partial_cmp(&other.bits)
    }
}

impl<T> cmp::Ord for Set<T>
where
    T: cmp::Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.bits.cmp(&other.bits)
    }
}

impl<T> Hash for Set<T>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bits.hash(state);
    }
}

impl<T> IntoIterator for Set<T>
where
    T: OwnedBits,
{
    type IntoIter = T::IntoBits;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.bits.into_bits()
    }
}

impl<'a, T> IntoIterator for &'a Set<T>
where
    T: OwnedBits,
{
    type IntoIter = T::IterBits<'a>;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_bits()
    }
}

impl<T> BitOr for Set<T>
where
    T: BitOr<Output = T>,
{
    type Output = Set<T>;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            bits: self.bits | rhs.bits,
        }
    }
}

impl<T> BitOrAssign for Set<T>
where
    T: BitOrAssign,
{
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.bits |= rhs.bits;
    }
}

impl<T> BitAnd for Set<T>
where
    T: BitAnd<Output = T>,
{
    type Output = Set<T>;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            bits: self.bits & rhs.bits,
        }
    }
}

impl<T> BitAndAssign for Set<T>
where
    T: BitAndAssign,
{
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.bits &= rhs.bits;
    }
}

impl<T> From<T> for Set<T> {
    #[inline]
    fn from(bits: T) -> Self {
        Set { bits }
    }
}
