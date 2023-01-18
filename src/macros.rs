/// Construct a bit set with specific values set using [`DefaultEndian`]
/// indexing.
///
/// [`DefaultEndian`]: crate::DefaultEndian
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set![0, 1, 3];
/// assert!(mask.iter_ones().eq([0, 1, 3]));
/// assert_eq!(mask, 0b00001011);
/// ```
///
/// Set ranges of bits:
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set![0..=4, 6..];
/// assert!(mask.iter_ones().eq([0, 1, 2, 3, 4, 6, 7]));
/// ```
#[macro_export]
macro_rules! set {
    (priv $set:ident {$_:ident},) => {};

    (priv-range $set:ident {$set_bit:ident}, $range:expr) => {{
        for index in $range {
            $crate::BitsMut::$set_bit(&mut $set, index);
        }
    }};

    (priv $set:ident {$($tt:tt)*}, $from:literal ..= $to:literal) => {{
        $crate::set!(priv-range $set {$($tt)*}, $from ..= $to);
    }};

    (priv $set:ident {$($tt:tt)*}, $from:literal ..= $to:literal, $($rest:tt)*) => {{
        $crate::set!(priv-range $set {$($tt)*}, $from ..= $to);
        $crate::set!(priv $set {$($tt)*}, $($rest)*);
    }};

    (priv $set:ident {$($tt:tt)*}, $from:literal .. $to:literal) => {{
        $crate::set!(priv-range $set {$($tt)*}, $from .. $to);
    }};

    (priv $set:ident {$($tt:tt)*}, $from:literal .. $to:literal, $($rest:tt)*) => {{
        $crate::set!(priv-range $set {$($tt)*}, $from .. $to);
        $crate::set!(priv $set {$($tt)*}, $($rest)*);
    }};

    (priv $set:ident {$($tt:tt)*}, $from:literal ..) => {{
        $crate::set!(priv-range $set {$($tt)*}, $from .. $crate::Bits::bits_capacity(&$set));
    }};

    (priv $set:ident {$($tt:tt)*}, $from:literal .., $($rest:tt)*) => {{
        $crate::set!(priv-range $set {$($tt)*}, $from .. $crate::Bits::bits_capacity(&$set));
        $crate::set!(priv $set {$($tt)*}, $($rest)*);
    }};

    (priv $set:ident {$set_bit:ident}, $index:expr) => {{
        $crate::BitsMut::$set_bit(&mut $set, $index);
    }};

    (priv $set:ident {$($tt:tt)*}, $index:expr, $($rest:tt)*) => {{
        $crate::set!(priv $set {$($tt)*}, $index);
        $crate::set!(priv $set {$($tt)*}, $($rest)*);
    }};

    ($($tt:tt)*) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $crate::set!(priv set {set_bit}, $($tt)*);
        set
    }};
}

/// Construct a bit set with specific values set using [`LittleEndian`]
/// indexing.
///
/// [`LittleEndian`]: crate::LittleEndian
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set_le![0, 1, 3];
/// assert!(mask.iter_ones_le().eq([0, 1, 3]));
/// assert_eq!(mask, 0b11010000);
/// ```
///
/// Set ranges of bits:
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set_le![0..=4, 6..];
/// assert!(mask.iter_ones_le().eq([0, 1, 2, 3, 4, 6, 7]));
/// assert_eq!(mask, 0b11111011);
/// ```
#[macro_export]
macro_rules! set_le {
    ($($tt:tt)*) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $crate::set!(priv set {set_bit_le}, $($tt)*);
        set
    }};
}

/// Construct a bit set with specific values set using [`BigEndian`]
/// indexing.
///
/// [`BigEndian`]: crate::BigEndian
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set_be![0, 1, 3];
/// assert!(mask.iter_ones_be().eq([0, 1, 3]));
/// assert_eq!(mask, 0b00001011);
/// ```
///
/// Set ranges of bits:
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set_be![0..=4, 6..];
/// assert!(mask.iter_ones_be().eq([0, 1, 2, 3, 4, 6, 7]));
/// assert_eq!(mask, 0b11011111);
/// ```
#[macro_export]
macro_rules! set_be {
    ($($tt:tt)*) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $crate::set!(priv set {set_bit_be}, $($tt)*);
        set
    }};
}
