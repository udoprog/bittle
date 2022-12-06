pub(crate) mod all;
pub(crate) mod none;

pub use self::all::All;
pub use self::none::None;

/// A trait used to check if an index is masked.
pub trait Mask: Sized {
    /// The iterator over a mask, indicating all items in the mask.
    type Iter: Iterator<Item = u32>;

    /// Test if the given bit is set.
    fn test(&self, index: u32) -> bool;

    /// Construct an iterator over a bit set.
    fn iter(&self) -> Self::Iter;

    /// Join this bit set with an iterator, creating an iterator that only
    /// yields the elements which are set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bittle::{FixedSet, Mask};
    ///
    /// let mask: FixedSet<u128> = bittle::fixed_set![0, 1, 3];
    /// let mut values = vec![false, false, false, false];
    ///
    /// for value in mask.join(values.iter_mut()) {
    ///     *value = true;
    /// }
    ///
    /// assert_eq!(values, vec![true, true, false, true]);
    /// ```
    fn join<I>(&self, iter: I) -> Join<Self::Iter, I::IntoIter>
    where
        Self: Sized,
        I: IntoIterator,
    {
        Join {
            mask: self.iter(),
            right: iter.into_iter(),
            last: 0,
        }
    }
}

impl<M: ?Sized> Mask for &'_ M
where
    M: Mask,
{
    type Iter = M::Iter;

    fn test(&self, index: u32) -> bool {
        (**self).test(index)
    }

    fn iter(&self) -> Self::Iter {
        (**self).iter()
    }
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
