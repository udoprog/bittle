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
    type BitsIter<'a>: Iterator<Item = u32>
    where
        Self: 'a;

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
    /// Elements which are out of bounds of the bit set will always return
    /// `false`.
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u8::full();
    /// assert!(!set.test(1024));
    ///
    /// let mut set = <[u8; 24]>::full();
    /// assert!(!set.test(1024));
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
    /// Setting a bit which is out of bounds does nothing.
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = 0u8;
    /// set.set(1024);
    /// assert!(set.is_empty());
    ///
    /// let mut set = [0u8; 24];
    /// set.set(1024);
    /// assert!(set.is_empty());
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
    /// Unsetting a bit which is out of bounds does nothing.
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let mut set = u8::full();
    /// set.unset(1024);
    /// assert!(set.is_full());
    ///
    /// let mut set = <[u8; 24]>::full();
    /// set.unset(1024);
    /// assert!(set.is_full());
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

    /// Construct the union between this and another set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a = 0u128;
    /// a.set(31);
    /// a.set(67);
    ///
    /// let mut b = 0u128;
    /// b.set(31);
    /// b.set(62);
    ///
    /// a.union(&b);
    ///
    /// assert!(a.test(31));
    /// assert!(a.test(62));
    /// assert!(a.test(67));
    /// ```
    fn union(&mut self, other: &Self);

    /// Construct the difference between this and another set.
    ///
    /// The empty set will contain elements which are exlusively contained in the
    /// second set. This is not a commutative operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut a = 0u128;
    /// a.set(31);
    /// a.set(67);
    ///
    /// let mut b = 0u128;
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
    fn difference(&mut self, other: &Self);

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
    /// let mut a = 0u128;
    /// a.set(31);
    /// a.set(67);
    ///
    /// let mut b = 0u128;
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
    fn symmetric_difference(&mut self, other: &Self);

    /// Construct an iterator over a bit set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = 0u128;
    ///
    /// set.set(3);
    /// set.set(7);
    ///
    /// assert_eq!(set.bits().collect::<Vec<_>>(), vec![3, 7]);
    /// ```
    ///
    /// A larger bit set:
    ///
    /// ```
    /// use bittle::Bits;
    ///
    /// let mut set = [0u32; 4];
    ///
    /// set.set(4);
    /// set.set(63);
    /// set.set(71);
    ///
    /// assert_eq!(set.bits().collect::<Vec<_>>(), vec![4, 63, 71]);
    /// ```
    fn bits(&self) -> Self::BitsIter<'_>;

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
    fn join<I>(&self, iter: I) -> Join<Self::BitsIter<'_>, I::IntoIter>
    where
        Self: Sized,
        I: IntoIterator,
    {
        Join {
            mask: self.bits(),
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
/// assert!(!a.bits().eq(b.bits()));
///
/// b.set(111);
/// assert!(a.bits().eq(b.bits()));
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
    type IntoBitsIter: Iterator<Item = u32>;

    /// Construct a empty bit set that is empty, where no element is set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{Bits, OwnedBits};
    ///
    /// let set = 0u128;
    ///
    /// assert!(set.is_empty());
    /// assert_eq!(set.bits().count(), 0);
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
    ///
    /// assert!(set.bits().eq(0..128))
    /// ```
    fn full() -> Self;

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
    fn into_bits(self) -> Self::IntoBitsIter;
}

/// A joined iterator.
///
/// Created using [Mask::join].
pub struct Join<A, B> {
    mask: A,
    right: B,
    last: u32,
}

impl<A, B> Iterator for Join<A, B>
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
