/// Construct a bit set with specific values set.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mask: u8 = bittle::set![0, 1, 3];
/// assert!(mask.iter_ones().eq([0, 1, 3]));
/// # #[cfg(bittle_shr)]
/// # assert_eq!(mask, 0b11010000);
/// # #[cfg(not(bittle_shr))]
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
