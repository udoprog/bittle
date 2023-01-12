use core::cmp;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Sub, SubAssign};

use crate::bits::Bits;
use crate::bits_mut::BitsMut;
use crate::bits_owned::BitsOwned;
use crate::shift::DefaultShift;
use crate::shift::Shift;

/// Convenience wrapper around bitsets providing the wrapped type with behaviors
/// you'd expected out of a set-like container.
///
/// <br>
///
/// ## Persistent shift ordering
///
/// A set can be constructed with a custom shift ordering that it remembers, so
/// that methods such as [`Bits::iter_ones`] uses the shift ordering in the
/// type.
///
/// ```
/// use bittle::{Bits, Set, Shr};
///
/// let set: Set<u16> = bittle::set![1, 12];
/// assert!(set.iter_ones().eq([1, 12]));
/// assert_eq!(set.into_bits(), 0b00010000_00000010);
///
/// let set: Set<u16, Shr> = bittle::set![1, 12];
/// assert!(set.iter_ones().eq([1, 12]));
/// assert_eq!(set.into_bits(), 0b01000000_00001000);
/// ```
///
/// <br>
///
/// ## Debugging
///
/// A reason one might want to use this wrapper is to have a [Debug][fmt::Debug]
/// implementation which shows which bits are actually in use:
///
/// ```
/// use bittle::{Bits, Set, Shr};
///
/// let set: u128 = bittle::set![1, 14];
/// assert_eq!(format!("{set:?}"), "16386");
///
/// let set: Set<u128> = Set::new(set);
/// assert_eq!(format!("{set:?}"), "{1, 14}");
///
/// let set: u128 = bittle::set_shr![1, 14];
/// assert_eq!(format!("{set:?}"), "85080976323951685521100712850600493056");
///
/// let set: Set<u128, Shr> = Set::new_with(set);
/// assert_eq!(format!("{set:?}"), "{1, 14}");
/// ```
///
/// <br>
///
/// ## Standard iteration
///
/// This wrapper provides unambigious implementations of [`IntoIterator`] which
/// delegates to [`Bits::iter_ones`], avoiding potential confusion when using an
/// array as a set:
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
#[repr(transparent)]
pub struct Set<T, S = DefaultShift>
where
    T: ?Sized,
{
    shift: PhantomData<S>,
    bits: T,
}

impl<T> Set<T> {
    /// Construct a set from its underlying bits using [`DefaultShift`].
    ///
    /// [`DefaultShift`]: crate::DefaultShift
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
        Self {
            shift: PhantomData,
            bits,
        }
    }
}

impl<T, S> Set<T, S> {
    /// Construct a set from its underlying bits using a custom shift ordering.
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
    pub const fn new_with(bits: T) -> Self {
        Self {
            shift: PhantomData,
            bits,
        }
    }

    /// Coerce into raw interior bits.
    #[inline]
    pub fn into_bits(self) -> T {
        self.bits
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

    /// Wrap a mutable reference as a set.
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

impl<T, S> Default for Set<T, S>
where
    T: BitsOwned,
    S: Shift,
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
    #[inline]
    fn default() -> Self {
        Self::new_with(T::ZEROS)
    }
}

impl<T, U> Bits for Set<T, U>
where
    T: ?Sized + Bits,
    U: Shift,
{
    type IterOnes<'a> = T::IterOnesWith<'a, U>
    where
        Self: 'a;

    type IterOnesWith<'a, S> = T::IterOnesWith<'a, S>
    where
        Self: 'a,
        S: Shift;

    type IterZeros<'a> = T::IterZerosWith<'a, U>
    where
        Self: 'a;

    type IterZerosWith<'a, S> = T::IterZerosWith<'a, S>
    where
        Self: 'a,
        S: Shift;

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
    fn test_bit_with<S>(&self, index: u32) -> bool
    where
        S: Shift,
    {
        self.bits.test_bit_with::<S>(index)
    }

    #[inline]
    fn test_bit(&self, index: u32) -> bool {
        self.bits.test_bit_with::<U>(index)
    }

    #[inline]
    fn iter_ones(&self) -> Self::IterOnes<'_> {
        self.bits.iter_ones_with()
    }

    #[inline]
    fn iter_ones_with<S>(&self) -> Self::IterOnesWith<'_, S>
    where
        S: Shift,
    {
        self.bits.iter_ones_with()
    }

    #[inline]
    fn iter_zeros(&self) -> Self::IterZeros<'_> {
        self.bits.iter_zeros_with()
    }

    #[inline]
    fn iter_zeros_with<S>(&self) -> Self::IterZerosWith<'_, S>
    where
        S: Shift,
    {
        self.bits.iter_zeros_with()
    }
}

impl<T, U> BitsMut for Set<T, U>
where
    T: ?Sized + BitsMut,
    U: Shift,
{
    #[inline]
    fn set_bit_with<S>(&mut self, index: u32)
    where
        S: Shift,
    {
        self.bits.set_bit_with::<S>(index);
    }

    #[inline]
    fn set_bit(&mut self, index: u32) {
        self.bits.set_bit_with::<U>(index);
    }

    #[inline]
    fn clear_bit_with<S>(&mut self, index: u32)
    where
        S: Shift,
    {
        self.bits.clear_bit_with::<S>(index);
    }

    #[inline]
    fn clear_bit(&mut self, index: u32) {
        self.bits.clear_bit_with::<U>(index);
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

impl<T, U> BitsOwned for Set<T, U>
where
    T: BitsOwned,
    U: Shift,
{
    const BITS: u32 = T::BITS;
    const ONES: Self = Self::new_with(T::ONES);
    const ZEROS: Self = Self::new_with(T::ZEROS);

    type IntoIterOnes = T::IntoIterOnesWith<U>;
    type IntoIterOnesWith<S> = T::IntoIterOnesWith<S> where S: Shift;
    type IntoIterZeros = T::IntoIterZerosWith<U>;
    type IntoIterZerosWith<S> = T::IntoIterZerosWith<S> where S: Shift;

    #[inline]
    fn zeros() -> Self {
        Self::new_with(T::ZEROS)
    }

    #[inline]
    fn ones() -> Self {
        Self::new_with(T::ONES)
    }

    #[inline]
    fn with_bit_with<S>(self, bit: u32) -> Self
    where
        S: Shift,
    {
        Self::new_with(self.bits.with_bit_with::<S>(bit))
    }

    #[inline]
    fn without_bit_with<S>(self, bit: u32) -> Self
    where
        S: Shift,
    {
        Self::new_with(self.bits.without_bit_with::<S>(bit))
    }

    #[inline]
    fn union(self, other: Self) -> Self {
        Self::new_with(self.bits.union(other.bits))
    }

    #[inline]
    fn conjunction(self, other: Self) -> Self {
        Self::new_with(self.bits.conjunction(other.bits))
    }

    #[inline]
    fn difference(self, other: Self) -> Self {
        Self::new_with(self.bits.difference(other.bits))
    }

    #[inline]
    fn symmetric_difference(self, other: Self) -> Self {
        Self::new_with(self.bits.symmetric_difference(other.bits))
    }

    #[inline]
    fn into_iter_ones(self) -> Self::IntoIterOnes {
        self.bits.into_iter_ones_with()
    }

    #[inline]
    fn into_iter_ones_with<S>(self) -> Self::IntoIterOnesWith<S>
    where
        S: Shift,
    {
        self.bits.into_iter_ones_with()
    }

    #[inline]
    fn into_iter_zeros(self) -> Self::IntoIterZeros {
        self.bits.into_iter_zeros_with()
    }

    #[inline]
    fn into_iter_zeros_with<S>(self) -> Self::IntoIterZerosWith<S>
    where
        S: Shift,
    {
        self.bits.into_iter_zeros_with()
    }
}

impl<T, S> Clone for Set<T, S>
where
    T: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            shift: PhantomData,
            bits: self.bits.clone(),
        }
    }
}

impl<T, S> Copy for Set<T, S> where T: Copy {}

impl<T, S> fmt::Debug for Set<T, S>
where
    T: ?Sized + Bits,
    S: Shift,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter_ones_with::<S>()).finish()
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
impl<T, U, S> cmp::PartialEq<U> for Set<T, S>
where
    T: ?Sized + Bits,
    U: ?Sized + Bits,
    S: Shift,
{
    #[inline]
    fn eq(&self, other: &U) -> bool {
        self.iter_ones_with::<S>().eq(other.iter_ones_with::<S>())
    }
}

impl<T, S> cmp::Eq for Set<T, S>
where
    T: ?Sized + Bits,
    S: Shift,
{
}

impl<T, U, S> cmp::PartialOrd<U> for Set<T, S>
where
    T: ?Sized + Bits,
    U: ?Sized + Bits,
    S: Shift,
{
    #[inline]
    fn partial_cmp(&self, other: &U) -> Option<cmp::Ordering> {
        self.iter_ones_with::<S>()
            .partial_cmp(other.iter_ones_with::<S>())
    }
}

impl<T, S> cmp::Ord for Set<T, S>
where
    T: ?Sized + Bits,
    S: Shift,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.iter_ones_with::<S>().cmp(other.iter_ones_with::<S>())
    }
}

impl<T, S> Hash for Set<T, S>
where
    T: ?Sized + Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bits.hash(state);
    }
}

impl<T, S> IntoIterator for Set<T, S>
where
    T: BitsOwned,
    S: Shift,
{
    type IntoIter = T::IntoIterOnesWith<S>;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.bits.into_iter_ones_with()
    }
}

impl<'a, T, S> IntoIterator for &'a Set<T, S>
where
    T: ?Sized + Bits,
    S: Shift,
{
    type IntoIter = T::IterOnesWith<'a, S>;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_ones_with::<S>()
    }
}

impl<T, S> From<T> for Set<T, S>
where
    T: BitsOwned,
    S: Shift,
{
    #[inline]
    fn from(bits: T) -> Self {
        Set {
            shift: PhantomData,
            bits,
        }
    }
}

macro_rules! owned_ops {
    ($trait:ident::$n:ident, $name:ident<$t:ident, $s:ident>, $fn:ident) => {
        impl<$t, $s> $trait<$name<$t, $s>> for $name<$t, $s>
        where
            $t: Copy + BitsOwned,
            $s: Shift,
        {
            type Output = $name<$t, $s>;

            #[inline]
            fn $n(self, rhs: $name<$t, $s>) -> Self::Output {
                $name::new_with(self.bits.$fn(rhs.bits))
            }
        }

        impl<$t, $s> $trait<&$name<$t, $s>> for $name<$t, $s>
        where
            $t: Copy + BitsOwned,
            $s: Shift,
        {
            type Output = $name<$t, $s>;

            #[inline]
            fn $n(self, rhs: &$name<$t, $s>) -> Self::Output {
                $name::new_with(self.bits.$fn(rhs.bits))
            }
        }

        impl<$t, $s> $trait<$name<$t, $s>> for &$name<$t, $s>
        where
            $t: Copy + BitsOwned,
            $s: Shift,
        {
            type Output = $name<$t, $s>;

            #[inline]
            fn $n(self, rhs: $name<$t, $s>) -> Self::Output {
                $name::new_with(self.bits.$fn(rhs.bits))
            }
        }

        impl<$t, $s> $trait<&$name<$t, $s>> for &$name<$t, $s>
        where
            $t: Copy + BitsOwned,
            $s: Shift,
        {
            type Output = $name<$t, $s>;

            #[inline]
            fn $n(self, rhs: &$name<$t, $s>) -> Self::Output {
                $name::new_with(self.bits.$fn(rhs.bits))
            }
        }
    };
}

macro_rules! assign_ops {
    ($trait:ident::$n:ident, $name:ident<$t:ident, $s:ident>, $fn:ident) => {
        impl<$t, $s> $trait<$name<$t, $s>> for $name<$t, $s>
        where
            $t: BitsMut,
        {
            #[inline]
            fn $n(&mut self, rhs: $name<$t, $s>) {
                self.bits.$fn(&rhs.bits);
            }
        }

        impl<$t, $s> $trait<&$name<$t, $s>> for $name<$t, $s>
        where
            $t: BitsMut,
        {
            #[inline]
            fn $n(&mut self, rhs: &$name<$t, $s>) {
                self.bits.$fn(&rhs.bits);
            }
        }

        impl<$t, $s> $trait<&$name<$t, $s>> for &mut $name<$t, $s>
        where
            $t: BitsMut,
        {
            #[inline]
            fn $n(&mut self, rhs: &$name<$t, $s>) {
                self.bits.$fn(&rhs.bits);
            }
        }
    };
}

owned_ops!(BitOr::bitor, Set<T, S>, union);
assign_ops!(BitOrAssign::bitor_assign, Set<T, S>, union_assign);
owned_ops!(BitAnd::bitand, Set<T, S>, conjunction);
assign_ops!(BitAndAssign::bitand_assign, Set<T, S>, conjunction_assign);
owned_ops!(BitXor::bitxor, Set<T, S>, symmetric_difference);
assign_ops!(
    BitXorAssign::bitxor_assign,
    Set<T, S>,
    symmetric_difference_assign
);
owned_ops!(Sub::sub, Set<T, S>, difference);
assign_ops!(SubAssign::sub_assign, Set<T, S>, difference_assign);
