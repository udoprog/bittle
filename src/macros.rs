/// Construct a bit set with specific values set.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mask: u128 = bittle::set![0, 1, 3];
///
/// assert!(mask.bit_test(0));
/// assert!(mask.bit_test(1));
/// assert!(!mask.bit_test(2));
/// assert!(mask.bit_test(3));
/// ```
#[macro_export]
macro_rules! set {
    ($($index:expr),* $(,)?) => {{
        let mut set = $crate::OwnedBits::ZEROS;
        $($crate::Bits::bit_set(&mut set, $index);)*
        set
    }};
}
