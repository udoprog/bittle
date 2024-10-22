use crate::Endian;

use super::Bits;

/// A joined iterator.
///
/// Created using [`Bits::join_ones`][crate::Bits::join_ones].
pub struct JoinOnes<'a, A, E, B>
where
    A: 'a + ?Sized + Bits,
    E: Endian,
{
    mask: A::IterOnesIn<'a, E>,
    iter: B,
    last: u32,
}

impl<'a, A, E, B> JoinOnes<'a, A, E, B>
where
    A: ?Sized + Bits,
    E: Endian,
{
    pub(crate) fn new(mask: A::IterOnesIn<'a, E>, iter: B) -> Self {
        Self {
            mask,
            iter,
            last: 0,
        }
    }
}

impl<'a, A, E, B> Iterator for JoinOnes<'a, A, E, B>
where
    A: 'a + ?Sized + Bits,
    E: Endian,
    B: Iterator,
{
    type Item = B::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.mask.next()?;
        let offset = index - self.last;
        let buf = self.iter.nth(offset as usize)?;
        self.last = index + 1;
        Some(buf)
    }
}
