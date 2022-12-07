use core::cmp;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;

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
/// assert_eq!(format!("{set:?}"), "85080976323951685521100712850600493056");
///
/// let set: Set<u128> = Set::new(set);
/// assert_eq!(format!("{set:?}"), "{1, 14}");
/// ```
///
/// This also provides unambigious implementations of [`IntoIterator`], whereas
/// arrays provide one themselves while primitive numbers do not.
///
/// Wrapping into a [Set] also provides us with [`BitOr`], [`BitAnd`],
/// [`BitXor`], and [`BitOrAssign`], [`BitAndAssign`], [`BitXorAssign`]
/// implementations to work with. They each refer to [`BitsOwned::union`],
/// [`BitsOwned::conjunction`], and [`BitsOwned::symmetric_difference`]
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
/// ```
///
/// It also ensures that all operations are bitwise, so it makes equality
/// checking two different kinds of sets possible:
///
/// ```
/// use bittle::Set;
/// assert_eq!(Set::new(0b00001000u8), Set::new(0b00001000_00000000u16));
/// assert_eq!(Set::new(0b00001000u8), Set::from_ref(&[0b00001000u8, 0b00000000u8]));
/// ```
///
/// # Examples
///
/// ```
/// use bittle::{Bits, BitsMut, BitsOwned, Set};
///
/// let mut a = Set::<u128>::zeros();
///
/// assert!(!a.bit_test(1));
/// a.bit_set(1);
/// assert!(a.bit_test(1));
/// a.bit_clear(1);
/// assert!(!a.bit_test(1));
/// ```
///
/// The bit set can also use arrays as its backing storage.
///
/// ```
/// use bittle::{Bits, BitsMut, BitsOwned, Set};
///
/// let mut a = Set::<[u64; 16]>::zeros();
///
/// assert!(!a.bit_test(172));
/// a.bit_set(172);
/// assert!(a.bit_test(172));
/// a.bit_clear(172);
/// assert!(!a.bit_test(172));
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
/// a.bit_set(111);
/// assert!(!a.iter_ones().eq(b.iter_ones()));
///
/// b.bit_set(111);
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
    /// assert!(set.iter_ones().eq([28, 31]));
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
    /// let mut set = Set::from_ref(&[0b10000000u8, 0b00001000u8]);
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
    /// let mut values = [0b10000000u8, 0b00001000u8];
    ///
    /// let mut set = Set::from_mut(&mut values);
    /// assert!(set.iter_ones().eq([0, 12]));
    /// set.bit_set(4);
    ///
    /// assert_eq!(&values[..], &[0b10001000u8, 0b00001000u8]);
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
    /// assert!(a.is_zeros());
    /// a.bit_set(0);
    /// assert!(!a.is_zeros());
    /// ```
    fn default() -> Self {
        Self { bits: T::ZEROS }
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
    fn bits_capacity(&self) -> u32 {
        self.bits.bits_capacity()
    }

    #[inline]
    fn is_ones(&self) -> bool {
        self.bits.is_ones()
    }

    #[inline]
    fn is_zeros(&self) -> bool {
        self.bits.is_zeros()
    }

    #[inline]
    fn bit_test(&self, index: u32) -> bool {
        self.bits.bit_test(index)
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
    fn bit_set(&mut self, index: u32) {
        self.bits.bit_set(index);
    }

    #[inline]
    fn bit_clear(&mut self, index: u32) {
        self.bits.bit_clear(index);
    }

    #[inline]
    fn bits_clear(&mut self) {
        self.bits.bits_clear();
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
/// assert_eq!(Set::new(0b00001000u8), Set::new(0b00001000_00000000u16));
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

impl<T> cmp::PartialOrd for Set<T>
where
    T: ?Sized + Bits,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
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
