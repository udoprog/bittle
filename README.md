# bittle

[<img alt="github" src="https://img.shields.io/badge/github-udoprog/bittle-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/bittle)
[<img alt="crates.io" src="https://img.shields.io/crates/v/bittle.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/bittle)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-bittle-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/bittle)
[<img alt="build status" src="https://img.shields.io/github/workflow/status/udoprog/bittle/CI/main?style=for-the-badge" height="20">](https://github.com/udoprog/bittle/actions?query=branch%3Amain)

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

<br>

## Examples

[Copy]: https://doc.rust-lang.org/std/marker/trait.Copy.html
[Mask]: https://docs.rs/bittle/latest/bittle/trait.Mask.html
[Mask::join]: https://docs.rs/bittle/latest/bittle/trait.Mask.html#method.join
