macro_rules! impl_iter {
    (
        $(#[$meta:meta])*
        {$($i:tt)*} $name:ident < $($lt:lifetime ,)? $($g:ident),* >
        {$build:ident, $assoc:path, $iter:path}
        {$var:ident : $var_ty:ty => $len:expr}
        {$($clone_bound:tt)*}
    ) => {
        $(#[$meta])*
        pub struct $name<$($lt ,)? $($i)*>
        where
            T: BitsOwned,
            E: Endian,
        {
            iter: $iter,
            head: Option<($assoc, u32)>,
            tail: Option<($assoc, u32)>,
        }

        impl<$($lt ,)? $($i)*> $name<$($lt ,)? $($g),*>
        where
            T: BitsOwned,
            E: Endian,
        {
            #[inline]
            pub(crate) fn new($var: $var_ty) -> Self {
                let mut iter = $var.into_iter();
                let head = iter.next().map(|v| (v.$build(), 0));

                let tail = iter.next_back().and_then(|v| {
                    let base = u32::try_from($len).ok()?.checked_sub(1)?.checked_mul(T::BITS)?;
                    Some((v.$build(), base))
                });

                Self { iter, head, tail }
            }
        }

        impl<$($lt ,)? $($i)*> Clone for $name<$($lt ,)? $($g),*>
        where
            T: BitsOwned,
            E: Endian,
            $assoc: Clone,
            $($clone_bound)*
        {
            #[inline]
            fn clone(&self) -> Self {
                Self {
                    iter: self.iter.clone(),
                    head: self.head.clone(),
                    tail: self.tail.clone(),
                }
            }
        }

        impl<$($lt ,)? $($i)*> Iterator for $name<$($lt ,)? $($g),*>
        where
            T: BitsOwned,
            E: Endian,
        {
            type Item = u32;

            fn next(&mut self) -> Option<Self::Item> {
                while let Some((index, o)) = $crate::internal::next_or_unset(&mut self.head, Iterator::next) {
                    if let index @ Some(_) = index {
                        return index;
                    }

                    self.head = self.iter.next().and_then(|v| Some((v.$build(), o.checked_add(T::BITS)?)));
                }

                let (index, _) = $crate::internal::next_or_unset(&mut self.tail, Iterator::next)?;
                index
            }
        }

        impl<$($lt ,)? $($i)*> DoubleEndedIterator for $name<$($lt ,)? $($g),*>
        where
            T: BitsOwned,
            $assoc: DoubleEndedIterator,
            E: Endian,
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                while let Some((index, o)) = $crate::internal::next_or_unset(&mut self.tail, DoubleEndedIterator::next_back) {
                    if let index @ Some(_) = index {
                        return index;
                    }

                    self.tail = self.iter.next_back().and_then(|v| Some((v.$build(), o.checked_sub(T::BITS)?)));
                }

                let (index, _) = $crate::internal::next_or_unset(&mut self.head, DoubleEndedIterator::next_back)?;
                index
            }
        }

        impl<$($lt ,)? $($i)*> core::iter::FusedIterator for $name<$($lt ,)? $($g),*>
        where
            T: BitsOwned,
            E: Endian,
        {
        }
    };
}

#[inline]
pub(crate) fn next_or_unset<I, F>(
    iter: &mut Option<(I, u32)>,
    advance: F,
) -> Option<(Option<u32>, u32)>
where
    F: FnOnce(&mut I) -> Option<u32>,
{
    let &mut Some((ref mut it, offset)) = iter else {
        return None;
    };

    let value = if let Some(index) = advance(it) {
        offset.checked_add(index)
    } else {
        *iter = None;
        None
    };

    Some((value, offset))
}
