//! Tests that bit sets without any capacity behave sensibly instead of
//! dividing by zero.
//!
//! A collection ends up without capacity either because it has no elements
//! (`[u8; 0]`, an empty slice) or because its element type itself has no
//! capacity (`[[u8; 0]; 4]`), and both cases have to be handled since the
//! indexing math divides by the element capacity and takes the remainder of the
//! element count.

use core::fmt::Debug;

use bittle::{BigEndian, Bits, BitsMut, BitsOwned, LittleEndian, Set};

/// Indexes probed by every test, including ones far outside of any bounds.
const INDEXES: [u32; 6] = [0, 1, 7, 8, 127, u32::MAX];

/// Assert every read operation on a bit set without capacity.
fn assert_reads<T>(bits: &T)
where
    T: ?Sized + Bits,
{
    assert_eq!(bits.bits_capacity(), 0);
    assert_eq!(bits.count_ones(), 0);
    assert_eq!(bits.count_zeros(), 0);

    // Vacuously true: there is no bit which is not one, and none which is not
    // zero.
    assert!(bits.all_ones());
    assert!(bits.all_zeros());

    assert!(bits.iter_ones().eq([]));
    assert!(bits.iter_ones_le().eq([]));
    assert!(bits.iter_ones_be().eq([]));
    assert!(bits.iter_zeros().eq([]));
    assert!(bits.iter_zeros_le().eq([]));
    assert!(bits.iter_zeros_be().eq([]));

    assert!(bits.join_ones(["a", "b", "c"]).eq(Vec::<&str>::new()));

    for index in INDEXES {
        // No bit is present, so no bit can be set.
        assert!(!bits.test_bit(index));
        assert!(!bits.test_bit_in::<LittleEndian>(index));
        assert!(!bits.test_bit_in::<BigEndian>(index));
        assert!(!bits.test_bit_le(index));
        assert!(!bits.test_bit_be(index));
    }
}

/// Assert every mutation on a bit set without capacity is a no-op.
fn assert_mutations<T>(bits: &mut T)
where
    T: ?Sized + BitsMut + Debug + PartialEq,
{
    for index in INDEXES {
        macro_rules! no_op {
            ($($call:expr),* $(,)?) => {
                $({
                    $call;
                    assert_reads(bits);
                })*
            };
        }

        no_op! {
            bits.set_bit(index),
            bits.set_bit_in::<LittleEndian>(index),
            bits.set_bit_in::<BigEndian>(index),
            bits.set_bit_le(index),
            bits.set_bit_be(index),
            bits.clear_bit(index),
            bits.clear_bit_in::<LittleEndian>(index),
            bits.clear_bit_in::<BigEndian>(index),
            bits.clear_bit_le(index),
            bits.clear_bit_be(index),
        }
    }

    bits.clear_bits();
    assert_reads(bits);
}

/// Assert the owned operations of a bit set without capacity.
fn assert_owned<T>()
where
    T: Copy + Debug + PartialEq + BitsOwned,
{
    assert_eq!(T::BITS, 0);

    let zeros = T::ZEROS;
    let ones = T::ONES;

    assert_eq!(T::zeros(), zeros);
    assert_eq!(T::ones(), ones);

    for bits in [zeros, ones] {
        assert_reads(&bits);

        let mut bits = bits;
        assert_mutations(&mut bits);

        assert!(bits.into_iter_ones().eq([]));
        assert!(bits.into_iter_ones_le().eq([]));
        assert!(bits.into_iter_ones_be().eq([]));
        assert!(bits.into_iter_zeros().eq([]));
        assert!(bits.into_iter_zeros_le().eq([]));
        assert!(bits.into_iter_zeros_be().eq([]));

        for index in INDEXES {
            assert_reads(&bits.with_bit(index));
            assert_reads(&bits.with_bit_in::<LittleEndian>(index));
            assert_reads(&bits.with_bit_in::<BigEndian>(index));
            assert_reads(&bits.with_bit_le(index));
            assert_reads(&bits.with_bit_be(index));
            assert_reads(&bits.without_bit(index));
            assert_reads(&bits.without_bit_in::<LittleEndian>(index));
            assert_reads(&bits.without_bit_in::<BigEndian>(index));
            assert_reads(&bits.without_bit_le(index));
            assert_reads(&bits.without_bit_be(index));
        }
    }

    // Set operations over empty sets stay empty.
    assert_reads(&zeros.union(ones));
    assert_reads(&zeros.conjunction(ones));
    assert_reads(&zeros.difference(ones));
    assert_reads(&zeros.symmetric_difference(ones));

    let mut bits = zeros;
    bits.union_assign(&ones);
    bits.conjunction_assign(&ones);
    bits.difference_assign(&ones);
    bits.symmetric_difference_assign(&ones);
    assert_reads(&bits);
}

/// Reverse iteration, which is bounded separately since it is not available
/// for every bit set.
#[test]
fn double_ended_iteration() {
    let a: [u8; 0] = [];
    assert!(a.iter_ones().rev().eq([]));
    assert!(a.iter_zeros().rev().eq([]));
    assert!(a.into_iter_ones().rev().eq([]));
    assert!(a.into_iter_zeros().rev().eq([]));

    let a: [[u8; 0]; 4] = [[]; 4];
    assert!(a.iter_ones().rev().eq([]));
    assert!(a.iter_zeros().rev().eq([]));
    assert!(a.into_iter_ones().rev().eq([]));
    assert!(a.into_iter_zeros().rev().eq([]));

    let a: &[u8] = &[];
    assert!(a.iter_ones().rev().eq([]));
    assert!(a.iter_zeros().rev().eq([]));

    let a: &[[u8; 0]] = &[[]; 4];
    assert!(a.iter_ones().rev().eq([]));
    assert!(a.iter_zeros().rev().eq([]));
}

/// An array with no elements.
#[test]
fn empty_array() {
    assert_owned::<[u8; 0]>();
    assert_owned::<[u128; 0]>();
}

/// An array whose element type has no capacity.
#[test]
fn array_of_empty_arrays() {
    assert_owned::<[[u8; 0]; 4]>();
    assert_owned::<[[u8; 0]; 0]>();
    assert_owned::<[[[u8; 0]; 4]; 4]>();
}

/// A slice with no elements.
#[test]
fn empty_slice() {
    let mut a: [u8; 0] = [];

    assert_reads(a.as_slice());
    assert_mutations(a.as_mut_slice());

    let mut a: [u128; 0] = [];

    assert_reads(a.as_slice());
    assert_mutations(a.as_mut_slice());
}

/// A slice whose element type has no capacity.
#[test]
fn slice_of_empty_arrays() {
    let mut a: [[u8; 0]; 4] = [[]; 4];

    assert_reads(a.as_slice());
    assert_mutations(a.as_mut_slice());
}

/// A vector routed through the slice implementation.
#[test]
fn empty_vec() {
    let mut a: Vec<u8> = Vec::new();

    assert_reads(a.as_slice());
    assert_mutations(a.as_mut_slice());

    let mut a: Vec<[u8; 0]> = vec![[]; 4];

    assert_reads(a.as_slice());
    assert_mutations(a.as_mut_slice());
}

/// Behind a reference, which delegates through a separate implementation.
#[test]
fn behind_reference() {
    let mut a: [u8; 0] = [];

    assert_reads(&&a);
    assert_mutations(&mut &mut a);

    let mut a: [[u8; 0]; 4] = [[]; 4];

    assert_reads(&&a);
    assert_mutations(&mut &mut a);
}

/// The [`Set`] wrapper, which delegates to the underlying bit set.
#[test]
fn set_wrapper() {
    assert_owned::<Set<[u8; 0]>>();
    assert_owned::<Set<[u8; 0], LittleEndian>>();
    assert_owned::<Set<[[u8; 0]; 4]>>();
    assert_owned::<Set<[[u8; 0]; 4], LittleEndian>>();

    let mut a: [u8; 0] = [];

    assert_reads(Set::<[u8]>::from_ref(a.as_slice()));
    assert_mutations(Set::<[u8]>::from_mut(a.as_mut_slice()));

    let mut a: [[u8; 0]; 4] = [[]; 4];

    assert_reads(Set::<[[u8; 0]]>::from_ref(a.as_slice()));
    assert_mutations(Set::<[[u8; 0]]>::from_mut(a.as_mut_slice()));
}

/// The `set!` family of macros, which sets bits through [`BitsMut`] and sizes
/// open ranges with [`Bits::bits_capacity`].
#[test]
fn set_macros() {
    let a: [u8; 0] = bittle::set![0, 7, 100, 0..10, 0..=10, 0..];
    assert_reads(&a);

    let a: [u8; 0] = bittle::set_le![0, 7, 100, 0..10, 0..=10, 0..];
    assert_reads(&a);

    let a: [u8; 0] = bittle::set_be![0, 7, 100, 0..10, 0..=10, 0..];
    assert_reads(&a);

    let a: [[u8; 0]; 4] = bittle::set![0, 7, 100, 0..10, 0..=10, 0..];
    assert_reads(&a);

    let a: [[u8; 0]; 4] = bittle::set_le![0, 7, 100, 0..10, 0..=10, 0..];
    assert_reads(&a);

    let a: [[u8; 0]; 4] = bittle::set_be![0, 7, 100, 0..10, 0..=10, 0..];
    assert_reads(&a);
}

/// Comparisons between empty sets of differing shapes, which go through
/// [`Bits::iter_ones`].
#[test]
fn comparisons() {
    let a: Set<[u8; 0]> = Set::new([]);
    let b: Set<[[u8; 0]; 4]> = Set::new([[]; 4]);
    let c: [u128; 0] = [];

    assert_eq!(a, b);
    assert_eq!(a, c);
    assert_eq!(a, Set::from_ref(&[] as &[u8]));

    // An empty set sorts before any non-empty one.
    assert!(a < Set::new(0b1u8));
    assert!(b < Set::new(0b1u8));

    assert_eq!(format!("{a:?}"), "{}");
    assert_eq!(format!("{b:?}"), "{}");
}
