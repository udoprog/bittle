/// A joined iterator.
///
/// Created using [Bits::join_ones][crate::Bits::join_ones].
pub struct JoinOnes<A, B> {
    mask: A,
    iter: B,
    last: u32,
}

impl<A, B> JoinOnes<A, B> {
    pub(crate) fn new(mask: A, iter: B) -> Self {
        Self {
            mask,
            iter,
            last: 0,
        }
    }
}

impl<A, B> Iterator for JoinOnes<A, B>
where
    A: Iterator<Item = u32>,
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
