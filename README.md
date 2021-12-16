# bittle

[![Documentation](https://docs.rs/bittle/badge.svg)](https://docs.rs/bittle)
[![Crates](https://img.shields.io/crates/v/bittle.svg)](https://crates.io/crates/bittle)
[![Actions Status](https://github.com/udoprog/bittle/workflows/Rust/badge.svg)](https://github.com/udoprog/bittle/actions)

A library for working with small and cheap bit sets and masks.

The name `bittle` comes from `bit` and `little`.

The bit sets are entirely defined using [Copy] types in Rust such as `u64`
or `[u128; 4]` who's number of bits define the capacity of the set.

```rust
use bittle::FixedSet;
use std::mem;

let mut set = FixedSet::<u64>::empty();

assert!(!set.test(31));
set.set(31);
assert!(set.test(31));
set.unset(31);
assert!(!set.test(31));

assert_eq!(mem::size_of_val(&set), mem::size_of::<u64>());
```

The [Mask] trait can be used to abstract over the read-only side of a bit
set. It has useful utilities such as iterating over masked elements through
[Mask::join].

```rust
use bittle::{FixedSet, Mask};

let elements = vec![10, 48, 101];
let mut m = FixedSet::<u128>::empty();

// Since set is empty, no elements are iterated over.
let mut it = m.join(&elements);
assert_eq!(it.next(), None);

m.set(1);

let mut it = m.join(&elements);
assert_eq!(it.next(), Some(&48));
assert_eq!(it.next(), None);
```

## Examples

[Copy]: https://doc.rust-lang.org/std/marker/trait.Copy.html
[Mask]: https://docs.rs/bittle/latest/bittle/trait.Mask.html
[Mask::join]: https://docs.rs/bittle/latest/bittle/trait.Mask.html#method.join

License: MIT/Apache-2.0
