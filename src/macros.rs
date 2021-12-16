/// Construct a bit set with specific values set.
///
/// # Examples
///
/// ```
/// use bittle::FixedSet;
///
/// let mask: FixedSet<u128> = bittle::fixed_set![0, 1, 3];
///
/// assert!(mask.test(0));
/// assert!(mask.test(1));
/// assert!(!mask.test(2));
/// assert!(mask.test(3));
/// ```
#[macro_export]
macro_rules! fixed_set {
    ($($set:expr),* $(,)?) => {
        $crate::FixedSet::from_array([$($set,)*])
    };
}
