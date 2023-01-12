/// Construct a bit set with specific values set using the default shift
/// indexing.
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
#[macro_export]
macro_rules! set {
    ($($index:expr),* $(,)?) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $($crate::BitsMut::set_bit(&mut set, $index);)*
        set
    }};
}

/// Construct a bit set with specific values set with [`Shr`].
///
/// [`Shr`]: crate::Shr
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set_shr![0, 1, 3];
/// assert!(mask.iter_ones_shr().eq([0, 1, 3]));
/// assert_eq!(mask, 0b11010000);
/// ```
#[macro_export]
macro_rules! set_shr {
    ($($index:expr),* $(,)?) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $($crate::BitsMut::set_bit_with::<$crate::Shr>(&mut set, $index);)*
        set
    }};
}
