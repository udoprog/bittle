use core::cmp;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Sub, SubAssign};

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;

/// Convenience wrapper around bitsets providing the wrapped type with behaviors
/// you'd expected out of a set-like container.
///
/// <br>
///
/// ## Debugging
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
/// let set: Set<u128> = Set::new(set);
/// assert_eq!(format!("{set:?}"), "{1, 14}");
/// ```
///
/// <br>
///
/// ## Standard iteration
///
/// This also provides unambigious implementations of [`IntoIterator`] which
/// delegates to [`Bits::iter_ones`] and the like avoiding potential confusion
/// when using an array as a set:
///
/// ```
/// use bittle::Set;
///
/// let array = [0b00001000u8, 0b0u8];
/// assert!(array.into_iter().eq([8, 0]));
///
/// let set = Set::new(array);
/// assert!(set.into_iter().eq([3]));
/// ```
///
/// <br>
///
/// ## Standard operators
///
/// Wrapping into a [Set] also provides us with [`BitOr`], [`BitAnd`],
/// [`BitXor`], [`Sub`], and [`BitOrAssign`], [`BitAndAssign`],
/// [`BitXorAssign`], [`SubAssign`] implementations to work with. They each
/// refer to [`BitsOwned::union`], [`BitsOwned::conjunction`],
/// [`BitsOwned::symmetric_difference`], and [`BitsOwned::difference`]
/// respectively.
///
/// ```
/// use bittle::{Bits, Set};
///
/// let set1: Set<[u32; 4]> = bittle::set![1, 65];
/// let set2: Set<[u32; 4]> = bittle::set![65, 110];
///
/// assert!((set1 | set2).iter_ones().eq([1, 65, 110]));
/// assert!((set1 & set2).iter_ones().eq([65]));
/// assert!((set1 ^ set2).iter_ones().eq([1, 110]));
/// assert!((set1 - set2).iter_ones().eq([1]));
///
/// let mut set3 = set1.clone();
/// set3 |= &set2;
/// assert!(set3.iter_ones().eq([1, 65, 110]));
///
/// let mut set3 = set1.clone();
/// set3 &= &set2;
/// assert!(set3.iter_ones().eq([65]));
///
/// let mut set3 = set1.clone();
/// set3 ^= &set2;
/// assert!(set3.iter_ones().eq([1, 110]));
///
/// let mut set3 = set1.clone();
/// set3 -= &set2;
/// assert!(set3.iter_ones().eq([1]));
/// ```
///
/// <br>
///
/// ## Equality and comparison
///
/// It also ensures that for operations that can be, are generic over bitwise
/// indexes, allowing different kinds of bitsets to be compared:
///
/// ```
/// use bittle::Set;
/// let a = 0b00000000_00000000_00000001_00010000u32;
/// let b = 0b00000001_00010000u16;
/// let c = vec![0b00010000u8, 0b00000001u8];
///
/// assert_eq!(Set::new(a), Set::new(b));
/// assert_eq!(Set::new(a), Set::from_ref(&c[..]));
///
/// let d = 0b00000001_11111111u16;
/// assert!(Set::new(d) < Set::new(a));
/// assert!(Set::new(d) < Set::new(b));
/// assert!(Set::new(d) < Set::from_ref(&c[..]));
/// ```
///
/// Note that if this result seems peculiar to you, consider that a bitset is
/// actually an *ordered set*, so it would mimic the behavior of
/// [`BTreeSet<u32>`] where `u32` are the indexes in
/// the set rather than a direct numerical comparison:
///
/// ```
/// use std::collections::BTreeSet;
/// let mut a = BTreeSet::new();
/// let mut b = BTreeSet::new();
///
/// a.insert(0u32);
/// a.insert(1u32);
/// b.insert(1u32);
///
/// assert!(a < b);
/// ```
///
/// [`BTreeSet<u32>`]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
///
/// # More Examples
///
/// ```
/// use bittle::{Bits, BitsMut, BitsOwned, Set};
///
/// let mut a = Set::<u128>::zeros();
///
/// assert!(!a.test_bit(1));
/// a.set_bit(1);
/// assert!(a.test_bit(1));
/// a.clear_bit(1);
/// assert!(!a.test_bit(1));
/// ```
///
/// The bit set can also use arrays as its backing storage.
///
/// ```
/// use bittle::{Bits, BitsMut, BitsOwned, Set};
///
/// let mut a = Set::<[u64; 16]>::zeros();
///
/// assert!(!a.test_bit(172));
/// a.set_bit(172);
/// assert!(a.test_bit(172));
/// a.clear_bit(172);
/// assert!(!a.test_bit(172));
/// ```
///
/// We can use the iterator of each set to compare bit sets of different kinds:
///
/// ```
/// use bittle::{Bits, BitsMut, BitsOwned, Set};
///
/// let mut a = Set::<[u64; 2]>::zeros();
/// let mut b = Set::<u128>::zeros();
///
/// a.set_bit(111);
/// assert!(!a.iter_ones().eq(b.iter_ones()));
///
/// b.set_bit(111);
/// assert!(a.iter_ones().eq(b.iter_ones()));
/// ```
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Set<T>
where
    T: ?Sized,
{
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
    /// let mut set = Set::new(0b00001001u32);
    /// assert!(set.iter_ones().eq([0, 3]));
    /// ```
    #[inline]
    pub const fn new(bits: T) -> Self {
        Self { bits }
    }
}

impl<T> Set<T>
where
    T: ?Sized,
{
    /// Wrap a reference as a set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, Set};
    ///
    /// let mut set = Set::from_ref(&[0b00000001u8, 0b00010000u8]);
    /// assert!(set.iter_ones().eq([0, 12]));
    /// ```
    #[inline]
    pub fn from_ref<U>(bits: &U) -> &Self
    where
        U: ?Sized + AsRef<T>,
    {
        // SAFETY: Reference provided as bits has the same memory layout as
        // &Set<T>.
        unsafe { &*(bits.as_ref() as *const _ as *const _) }
    }

    /// Wrap a mutable reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, Set};
    ///
    /// let mut values = [0b00000001u8, 0b00010000u8];
    ///
    /// let mut set = Set::from_mut(&mut values);
    /// assert!(set.iter_ones().eq([0, 12]));
    ///
    /// set.set_bit(4);
    /// assert_eq!(&values[..], &[0b00010001u8, 0b00010000u8]);
    /// ```
    #[inline]
    pub fn from_mut<U>(bits: &mut U) -> &mut Self
    where
        U: ?Sized + AsMut<T>,
    {
        // SAFETY: Reference provided as bits has the same memory layout as &mut
        // Set<T>.
        unsafe { &mut *(bits.as_mut() as *mut _ as *mut _) }
    }
}

impl<T> Default for Set<T>
where
    T: BitsOwned,
{
    /// Construct a new empty set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, BitsMut, BitsOwned, Set};
    ///
    /// let mut a = Set::<u32>::zeros();
    ///
    /// assert!(a.all_zeros());
    /// a.set_bit(0);
    /// assert!(!a.all_zeros());
    /// ```
    fn default() -> Self {
        Self { bits: T::ZEROS }
    }
}

impl<T> Bits for Set<T>
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
        self.bits.count_ones()
    }

    #[inline]
    fn count_zeros(&self) -> u32 {
        self.bits.count_zeros()
    }

    #[inline]
    fn bits_capacity(&self) -> u32 {
        self.bits.bits_capacity()
    }

    #[inline]
    fn all_ones(&self) -> bool {
        self.bits.all_ones()
    }

    #[inline]
    fn all_zeros(&self) -> bool {
        self.bits.all_zeros()
    }

    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        self.bits.test_bit(index)
    }

    #[inline]
    fn iter_ones(&self) -> T::IterOnes<'_> {
        self.bits.iter_ones()
    }

    #[inline]
    fn iter_zeros(&self) -> T::IterZeros<'_> {
        self.bits.iter_zeros()
    }
}

impl<T> BitsMut for Set<T>
where
    T: ?Sized + BitsMut,
{
    #[inline]
    fn set_bit(&mut self, index: u32) {
        self.bits.set_bit(index);
    }

    #[inline]
    fn clear_bit(&mut self, index: u32) {
        self.bits.clear_bit(index);
    }

    #[inline]
    fn clear_bits(&mut self) {
        self.bits.clear_bits();
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
}

impl<T> BitsOwned for Set<T>
where
    T: BitsOwned,
{
    const BITS: u32 = T::BITS;
    const ONES: Self = Self { bits: T::ONES };
    const ZEROS: Self = Self { bits: T::ZEROS };

    type IntoIterOnes = T::IntoIterOnes;
    type IntoIterZeros = T::IntoIterZeros;

    #[inline]
    fn zeros() -> Self {
        Self { bits: T::ZEROS }
    }

    #[inline]
    fn ones() -> Self {
        Self { bits: T::ONES }
    }

    #[inline]
    fn with_bit(self, bit: u32) -> Self {
        Self {
            bits: self.bits.with_bit(bit),
        }
    }

    #[inline]
    fn without_bit(self, bit: u32) -> Self {
        Self {
            bits: self.bits.without_bit(bit),
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
    fn into_iter_ones(self) -> T::IntoIterOnes {
        self.bits.into_iter_ones()
    }

    #[inline]
    fn into_iter_zeros(self) -> T::IntoIterZeros {
        self.bits.into_iter_zeros()
    }
}

impl<T> fmt::Debug for Set<T>
where
    T: ?Sized + Bits,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter_ones()).finish()
    }
}

/// Flexible [`PartialEq`] implementation which allows for comparisons between different kinds of sets.
///
/// # Examples
///
/// ```
/// use bittle::Set;
///
/// let a = Set::new(0b00001000u8);
/// let b = Set::new(0b00000000_00001000u16);
/// let c = Set::new([0b00001000u8, 0]);
///
/// assert_eq!(a, b);
/// assert_eq!(a, c);
/// ```
impl<T, U> cmp::PartialEq<U> for Set<T>
where
    T: ?Sized + Bits,
    U: ?Sized + Bits,
{
    #[inline]
    fn eq(&self, other: &U) -> bool {
        self.iter_ones().eq(other.iter_ones())
    }
}

impl<T> cmp::Eq for Set<T> where T: ?Sized + Bits {}

impl<T, U> cmp::PartialOrd<U> for Set<T>
where
    T: ?Sized + Bits,
    U: ?Sized + Bits,
{
    #[inline]
    fn partial_cmp(&self, other: &U) -> Option<cmp::Ordering> {
        self.iter_ones().partial_cmp(other.iter_ones())
    }
}

impl<T> cmp::Ord for Set<T>
where
    T: ?Sized + Bits,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.iter_ones().cmp(other.iter_ones())
    }
}

impl<T> Hash for Set<T>
where
    T: ?Sized + Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bits.hash(state);
    }
}

impl<T> IntoIterator for Set<T>
where
    T: BitsOwned,
{
    type IntoIter = T::IntoIterOnes;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.bits.into_iter_ones()
    }
}

impl<'a, T> IntoIterator for &'a Set<T>
where
    T: ?Sized + Bits,
{
    type IntoIter = T::IterOnes<'a>;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_ones()
    }
}

impl<T> From<T> for Set<T>
where
    T: BitsOwned,
{
    #[inline]
    fn from(bits: T) -> Self {
        Set { bits }
    }
}

macro_rules! owned_ops {
    ($trait:ident::$n:ident, $name:ident<$t:ident>, $fn:ident) => {
        impl<$t> $trait<$name<$t>> for $name<$t>
        where
            $t: Copy + BitsOwned,
        {
            type Output = $name<$t>;

            #[inline]
            fn $n(self, rhs: $name<$t>) -> Self::Output {
                $name {
                    bits: self.bits.$fn(rhs.bits),
                }
            }
        }

        impl<$t> $trait<&$name<$t>> for $name<$t>
        where
            $t: Copy + BitsOwned,
        {
            type Output = $name<$t>;

            #[inline]
            fn $n(self, rhs: &$name<$t>) -> Self::Output {
                $name {
                    bits: self.bits.$fn(rhs.bits),
                }
            }
        }

        impl<$t> $trait<$name<$t>> for &$name<$t>
        where
            $t: Copy + BitsOwned,
        {
            type Output = $name<$t>;

            #[inline]
            fn $n(self, rhs: $name<$t>) -> Self::Output {
                $name {
                    bits: self.bits.$fn(rhs.bits),
                }
            }
        }

        impl<$t> $trait<&$name<$t>> for &$name<$t>
        where
            $t: Copy + BitsOwned,
        {
            type Output = $name<$t>;

            #[inline]
            fn $n(self, rhs: &$name<$t>) -> Self::Output {
                $name {
                    bits: self.bits.$fn(rhs.bits),
                }
            }
        }
    };
}

macro_rules! assign_ops {
    ($trait:ident::$n:ident, $name:ident<$t:ident>, $fn:ident) => {
        impl<$t> $trait<$name<$t>> for $name<$t>
        where
            $t: BitsMut,
        {
            #[inline]
            fn $n(&mut self, rhs: $name<$t>) {
                self.bits.$fn(&rhs.bits);
            }
        }

        impl<$t> $trait<&$name<$t>> for $name<$t>
        where
            $t: BitsMut,
        {
            #[inline]
            fn $n(&mut self, rhs: &$name<$t>) {
                self.bits.$fn(&rhs.bits);
            }
        }

        impl<$t> $trait<&$name<$t>> for &mut $name<$t>
        where
            $t: BitsMut,
        {
            #[inline]
            fn $n(&mut self, rhs: &$name<$t>) {
                self.bits.$fn(&rhs.bits);
            }
        }
    };
}

owned_ops!(BitOr::bitor, Set<T>, union);
assign_ops!(BitOrAssign::bitor_assign, Set<T>, union_assign);
owned_ops!(BitAnd::bitand, Set<T>, conjunction);
assign_ops!(BitAndAssign::bitand_assign, Set<T>, conjunction_assign);
owned_ops!(BitXor::bitxor, Set<T>, symmetric_difference);
assign_ops!(
    BitXorAssign::bitxor_assign,
    Set<T>,
    symmetric_difference_assign
);
owned_ops!(Sub::sub, Set<T>, difference);
assign_ops!(SubAssign::sub_assign, Set<T>, difference_assign);
