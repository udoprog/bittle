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
#[macro_export]
macro_rules! set {
    ($($index:expr),* $(,)?) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $($crate::BitsMut::set_bit(&mut set, $index);)*
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
#[macro_export]
macro_rules! set_le {
    ($($index:expr),* $(,)?) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $($crate::BitsMut::set_bit_le(&mut set, $index);)*
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
#[macro_export]
macro_rules! set_be {
    ($($index:expr),* $(,)?) => {{
        let mut set = $crate::BitsOwned::ZEROS;
        $($crate::BitsMut::set_bit_be(&mut set, $index);)*
        set
    }};
}
