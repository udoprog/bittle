/// Construct a bit set with specific values set.
///
/// # Examples
///
/// ```
/// use bittle::Bits;
///
/// let mask: u128 = bittle::set![0, 1, 3];
///
/// assert!(mask.test(0));
/// assert!(mask.test(1));
/// assert!(!mask.test(2));
/// assert!(mask.test(3));
/// ```
#[macro_export]
macro_rules! set {
    ($($index:expr),* $(,)?) => {{
        let mut set = $crate::OwnedBits::EMPTY;
        $($crate::Bits::set(&mut set, $index);)*
        set
    }};
}
