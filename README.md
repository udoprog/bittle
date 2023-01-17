# bittle

[<img alt="github" src="https://img.shields.io/badge/github-udoprog/bittle-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/bittle)
[<img alt="crates.io" src="https://img.shields.io/crates/v/bittle.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/bittle)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-bittle-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/bittle)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/udoprog/bittle/ci.yml?branch=main&style=for-the-badge" height="20">](https://github.com/udoprog/bittle/actions?query=branch%3Amain)

Zero-cost bitsets over native Rust types.

The name `bittle` comes from `bit` and `little`. Small bitsets!

<br>

## Usage

Add `bittle` as a dependency in your `Cargo.toml`:

<br>

```toml
[dependencies]
bittle = "0.5.3"
```

<br>

## Guide

A bit is always identified by a [`u32`] by its index, and the exact location
for a bit in a primitive numbers is defined by its endianness, which is
[`BigEndian`] by default.

[`BigEndian`] indexing grows from right to left, such as the following
[`u8`] literal:

```text
0b0010_0010u8
    ^    ^- index 1
    '------ index 5
```

<br>

To interact with these bits we define the [`Bits`], [`BitsMut`], and
[`BitsOwned`] traits. These traits are implemented for primitive types such
as `u32`, `[u32; 4]`, or `&[u32]`:

```rust
use bittle::Bits;

let array: [u32; 4] = [0, 1, 2, 3];
assert!(array.iter_ones().eq([32, 65, 96, 97]));

let n = 0b00000000_00000000_00000000_00010001u32;
assert!(n.iter_ones().eq([0, 4]));

let array_of_arrays: [[u8; 4]; 2] = [[16, 0, 0, 0], [0, 0, 1, 0]];
assert!(array_of_arrays.iter_ones().eq([4, 48]));

let mut vec: Vec<u32> = vec![0, 1, 2, 3];
assert!(vec.iter_ones().eq([32, 65, 96, 97]));
```

<br>

We also provide the [`set!`] macro, which is a zero-cost convenience method
for constructing primitive forms of bit sets:

```rust
use bittle::Bits;

let array: [u32; 4] = bittle::set![32, 65, 96, 97];
assert!(array.iter_ones().eq([32, 65, 96, 97]));

let n: u32 = bittle::set![0, 4];
assert!(n.iter_ones().eq([0, 4]));

let array_of_arrays: [[u8; 4]; 2] = bittle::set![4, 48];
assert!(array_of_arrays.iter_ones().eq([4, 48]));
```

<br>

Since a vector is not a primitive bit set, it could instead make use of
[`BitsMut`] directly:

```rust
use bittle::{Bits, BitsMut};

let mut vec: Vec<u32> = vec![0u32; 4];
vec.set_bit(32);
vec.set_bit(65);
vec.set_bit(96);
vec.set_bit(97);
assert!(vec.iter_ones().eq([32, 65, 96, 97]));
assert_eq!(vec, [0, 1, 2, 3]);
```

<br>

Due to how broadly these traits are implemented, we also try to avoid using
names which are commonly used in other APIs, instead opt for bit-specific
terminology such as:

* Something like `is_empty` becomes `all_zeros` - since with bits you're
  thinking about "ones and zeros".
* Testing if a bit is set is `test_bit`, or in general adding the `*_bit`
  suffix to operations over individual bits.
* Clearing all bits becomes `clear_bits`, or in general adding the `*_bits`
  suffix when operating over *all* bits.

```rust
use bittle::{Bits, BitsMut};

let mut set = [0u16; 2];

set.set_bit(15);
assert!(set.test_bit(15));

set.union_assign(&bittle::set![31, 7]);
assert!(set.test_bit(31) && set.test_bit(7));

set.clear_bit(31);
assert!(!set.test_bit(31));

set.clear_bits();
assert!(set.all_zeros());
```

<br>

Some other interesting operations, such as [`Bits::join_ones`] are available,
allowing bitsets to act like masks over other iterators:

```rust
use bittle::{Bits, BitsMut};

let elements = vec![10, 48, 101];
let mut m = 0u128;

m.set_bit(0);
assert!(m.join_ones(&elements).eq([&10]));
m.set_bit(2);
assert!(m.join_ones(&elements).eq([&10, &101]));
```

<br>

[`BigEndian`]: https://docs.rs/bittle/latest/bittle/struct.BigEndian.html
[`Bits::join_ones`]: https://docs.rs/bittle/latest/bittle/trait.Bits.html#method.join_ones
[`Bits::test_bit_in`]: https://docs.rs/bittle/latest/bittle/trait.Bits.html#method.test_bit_in
[`Bits::test_bit_le`]: https://docs.rs/bittle/latest/bittle/trait.Bits.html#method.test_bit_le
[`Bits`]: https://docs.rs/bittle/latest/bittle/trait.Bits.html
[`BitsMut`]: https://docs.rs/bittle/latest/bittle/trait.BitsMut.html
[`BitsOwned`]: https://docs.rs/bittle/latest/bittle/trait.BitsOwned.html
[`Copy`]: https://doc.rust-lang.org/std/marker/trait.Copy.html
[`set!`]: https://docs.rs/bittle/latest/bittle/macro.set.html
[`u32`]: https://doc.rust-lang.org/std/primitive.u32.html
[`u8`]: https://doc.rust-lang.org/std/primitive.u8.html
[see issue #2]: https://github.com/udoprog/bittle/pull/2
