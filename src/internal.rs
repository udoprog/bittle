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
                loop {
                    if let Some((it, offset)) = &mut self.head {
                        let offset = *offset;

                        if let Some(index) = it.next() {
                            return offset.checked_add(index);
                        }

                        self.head = None;

                        if let Some(value) = self.iter.next() {
                            let bits = value.bits_capacity();
                            self.head = Some((value.$build(), offset.checked_add(bits)?));
                            continue;
                        }
                    }

                    if let Some((it, offset)) = &mut self.tail {
                        let offset = *offset;

                        if let Some(index) = it.next() {
                            return offset.checked_add(index);
                        }

                        self.tail = None;
                    }

                    return None;
                }
            }
        }

        impl<$($lt ,)? $($i)*> DoubleEndedIterator for $name<$($lt ,)? $($g),*>
        where
            T: BitsOwned,
            $assoc: DoubleEndedIterator,
            E: Endian,
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                loop {
                    if let Some((it, offset)) = &mut self.tail {
                        let offset = *offset;

                        if let Some(index) = it.next_back() {
                            return offset.checked_add(index);
                        }

                        self.tail = None;

                        if let Some(value) = self.iter.next_back() {
                            self.tail = Some((value.$build(), offset.checked_sub(T::BITS)?));
                            continue;
                        }
                    }

                    if let Some((it, offset)) = &mut self.head {
                        let offset = *offset;

                        if let Some(index) = it.next_back() {
                            return offset.checked_add(index);
                        }

                        self.head = None;
                    }

                    return None;
                }
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
