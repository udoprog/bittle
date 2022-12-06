//! A fixed size bit set.

/// Bitset operations.
///
/// This is implemented for primitive types such as:
/// * [`usize`], [`u32`], [`u64`], and other signed numbers.
/// * Arrays made up of numerical primitives, such as `[u32; 32]`.
/// * Slices of numerical primitives, such as `&[u32]`.
///
/// This does not include owned operations such as turning the bit set into an
/// owned iterator using [OwnedBits::into_bits], for more like that see
/// [OwnedBits].
pub trait Bits {
    /// The iterator over this bit pattern.
    ///
    /// See [Bits::bits].
    type IterBits<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    /// Get the length of the bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = 0u128;
    /// assert_eq!(set.len(), 0);
    /// set.set(4);
    /// assert_eq!(set.len(), 1);
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = [0u128, 0];
    /// assert_eq!(set.len(), 0);
    /// set.set(240);
    /// assert_eq!(set.len(), 1);
    /// ```
    fn len(&self) -> u32;

    /// Get the capacity of the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = 0u128;
    /// assert_eq!(set.capacity(), 128);
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = [0u128, 0];
    /// assert_eq!(set.capacity(), 256);
    /// ```
    fn capacity(&self) -> u32;

    /// Test if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = 0u128;
    /// assert!(set.is_empty());
    /// set.set(4);
    /// assert!(!set.is_empty());
    /// ```
    ///
    /// With arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = [0u128; 2];
    /// assert!(set.is_empty());
    /// set.set(250);
    /// assert!(!set.is_empty());
    /// ```
    fn is_empty(&self) -> bool;

    /// Test if this set is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u128::full();
    /// assert!(set.is_full());
    /// set.unset(4);
    /// assert!(!set.is_full());
    /// ```
    fn is_full(&self) -> bool;

    /// Test if the given bit is set.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = 0u32;
    /// assert!(!set.test(32));
    /// set.set(0);
    /// assert!(set.test(32));
    /// set.unset(32);
    /// assert!(!set.test(0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u128::full();
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
    fn test(&self, index: u32) -> bool;

    /// Set the given bit.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = 0u32;
    /// assert!(!set.test(32));
    /// set.set(0);
    /// assert!(set.test(32));
    /// set.unset(32);
    /// assert!(!set.test(0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u128::full();
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
    fn set(&mut self, index: u32);

    /// Unset the given bit.
    ///
    /// Indexes which are out of bounds will wrap around in the bitset.
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = 0u32;
    /// assert!(!set.test(32));
    /// set.set(0);
    /// assert!(set.test(32));
    /// set.unset(32);
    /// assert!(!set.test(0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u128::full();
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
    fn unset(&mut self, index: u32);

    /// Clear the entire bit pattern.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u128::full();
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
    fn clear(&mut self);

    /// Modify the current set in place so that it becomes a union of this and
    /// another set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// a.conjunction_assign(&b);
    ///
    /// assert!(a.iter_bits().eq([31]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// a.conjunction_assign(&b);
    ///
    /// assert!(a.iter_bits().eq([31]));
    /// ```
    fn conjunction_assign(&mut self, other: &Self);

    /// Modify the current set in place so that it becomes a union of this and
    /// another set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// a.union_assign(&b);
    ///
    /// assert!(a.iter_bits().eq([31, 62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// a.union_assign(&b);
    ///
    /// assert!(a.iter_bits().eq([31, 62, 67]));
    /// ```
    fn union_assign(&mut self, other: &Self);

    /// Construct the difference between this and another set.
    ///
    /// This assigns the elements in the second set which are not part of the
    /// first.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let mut c = a;
    /// c.difference_assign(&b);
    ///
    /// let mut d = b;
    /// d.difference_assign(&a);
    ///
    /// assert_ne!(c, d);
    ///
    /// assert!(c.iter_bits().eq([62]));
    /// assert!(d.iter_bits().eq([67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let mut c = a;
    /// c.difference_assign(&b);
    ///
    /// let mut d = b;
    /// d.difference_assign(&a);
    ///
    /// assert_ne!(c, d);
    ///
    /// assert!(c.iter_bits().eq([62]));
    /// assert!(d.iter_bits().eq([67]));
    /// ```
    fn difference_assign(&mut self, other: &Self);

    /// Construct the symmetric difference between this and another set.
    ///
    /// The empty set will contain elements which exist exclusively in one or the
    /// other.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// a.symmetric_difference_assign(&b);
    ///
    /// assert!(a.iter_bits().eq([62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// a.symmetric_difference_assign(&b);
    ///
    /// assert!(a.iter_bits().eq([62, 67]));
    /// ```
    fn symmetric_difference_assign(&mut self, other: &Self);

    /// Construct an iterator over a bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: u128 = bittle::set![3, 7];
    /// assert!(set.iter_bits().eq([3, 7]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let set: [u32; 4] = bittle::set![4, 67, 71];
    /// assert!(set.iter_bits().eq([4, 67, 71]));
    /// ```
    fn iter_bits(&self) -> Self::IterBits<'_>;

    /// Join this bit set with an iterator, creating an iterator that only
    /// yields the elements which are set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mask: u128 = bittle::set![0, 1, 3];
    /// let mut values = vec![false, false, false, false];
    ///
    /// for value in mask.join(values.iter_mut()) {
    ///     *value = true;
    /// }
    ///
    /// assert_eq!(values, vec![true, true, false, true]);
    /// ```
    fn join<I>(&self, iter: I) -> IterJoin<Self::IterBits<'_>, I::IntoIter>
    where
        Self: Sized,
        I: IntoIterator,
    {
        IterJoin {
            mask: self.iter_bits(),
            right: iter.into_iter(),
            last: 0,
        }
    }
}

/// Trait which abstracts over type capable of representing owned bit sets.
///
/// This extends [Bits] and adds the necessary capabilities to generically
/// construct a bit set instead of only operating over it.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mut set = 0u128;
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
/// use bittle::Bits;
///
/// let mut set = [0u64; 16];
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
/// use bittle::Bits;
///
/// let mut a = [0u64; 2];
/// let mut b = 0u128;
///
/// a.set(111);
/// assert!(!a.iter_bits().eq(b.iter_bits()));
///
/// b.set(111);
/// assert!(a.iter_bits().eq(b.iter_bits()));
/// ```
pub trait OwnedBits: Bits {
    /// Full number of bits in the set.
    const BITS: u32;

    /// Bit-pattern for an empty bit pattern.
    ///
    /// See [OwnedBits::empty].
    const EMPTY: Self;

    /// Bit-pattern for a full bit pattern.
    ///
    /// See [OwnedBits::full].
    const FULL: Self;

    /// Owning iterator over bits.
    ///
    /// See [OwnedBits::into_bits].
    type IntoBits: Iterator<Item = u32>;

    /// Construct a empty bit set that is empty, where no element is set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let set = 0u128;
    /// assert!(set.is_empty());
    /// assert_eq!(set.iter_bits().count(), 0);
    /// ```
    fn empty() -> Self;

    /// Construct a empty bit set that is full, where every single element
    /// possible is set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let set = u128::full();
    /// assert!(set.iter_bits().eq(0..128))
    /// ```
    fn full() -> Self;

    /// Set the given bit and return the modified set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let set = u128::empty().with(8).with(12);
    /// assert!(set.iter_bits().eq([8, 12]))
    /// ```
    fn with(self, bit: u32) -> Self;

    /// Construct the union between this and another set.
    ///
    /// This retains all elements from both sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.union(b);
    /// assert!(c.iter_bits().eq([31, 62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.union(b);
    /// assert!(c.iter_bits().eq([31, 62, 67]));
    /// ```
    fn union(self, other: Self) -> Self;

    /// Constructs the conjunctionunction between this and another set.
    ///
    /// This retains elements which are common to both sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.conjunction(b);
    /// assert!(c.iter_bits().eq([31]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.conjunction(b);
    /// assert!(c.iter_bits().eq([31]));
    /// ```
    fn conjunction(self, other: Self) -> Self;

    /// Construct the difference between this and another set.
    ///
    /// This returns the elements in the second set which are not part of the
    /// first.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Set, Bits, OwnedBits};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.difference(b);
    /// assert!(c.iter_bits().eq([62]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.difference(b);
    /// assert!(c.iter_bits().eq([62]));
    /// ```
    fn difference(self, other: Self) -> Self;

    /// Construct the symmetric difference between this and another set.
    ///
    /// This retains elements which are unique to each set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let a: u128 = bittle::set![31, 67];
    /// let b: u128 = bittle::set![31, 62];
    ///
    /// let c = a.symmetric_difference(b);
    /// assert!(c.iter_bits().eq([62, 67]));
    /// ```
    ///
    /// Using arrays:
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let a: [u32; 4] = bittle::set![31, 67];
    /// let b: [u32; 4] = bittle::set![31, 62];
    ///
    /// let c = a.symmetric_difference(b);
    /// assert!(c.iter_bits().eq([62, 67]));
    /// ```
    fn symmetric_difference(self, other: Self) -> Self;

    /// Construct an owning iterator over a bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = 0u128;
    ///
    /// set.set(3);
    /// set.set(7);
    ///
    /// assert!(set.into_bits().eq([3, 7]));
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = [0u32; 4];
    ///
    /// set.set(4);
    /// set.set(63);
    /// set.set(71);
    ///
    /// assert!(set.into_bits().eq([4, 63, 71]));
    /// ```
    fn into_bits(self) -> Self::IntoBits;
}

/// A joined iterator.
///
/// Created using [Mask::join].
pub struct IterJoin<A, B> {
    mask: A,
    right: B,
    last: u32,
}

impl<A, B> Iterator for IterJoin<A, B>
where
    A: Iterator<Item = u32>,
    B: Iterator,
{
    type Item = B::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.mask.next()?;
        let offset = index - self.last;
        let buf = self.right.nth(offset as usize)?;
        self.last = index + 1;
        Some(buf)
    }
}
