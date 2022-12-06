//! [<img alt="github" src="https://img.shields.io/badge/github-udoprog/bittle-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/bittle)
//! [<img alt="crates.io" src="https://img.shields.io/crates/v/bittle.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/bittle)
//! [<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-bittle-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/bittle)
//! [<img alt="build status" src="https://img.shields.io/github/workflow/status/udoprog/bittle/CI/main?style=for-the-badge" height="20">](https://github.com/udoprog/bittle/actions?query=branch%3Amain)
//!
//! A library for working with bitsets.
//!
//! The name `bittle` comes from `bit` and `little`. Small bitsets!
//!
//! This crate defines the [Bits] and [OwnedBits] traits which allows for
//! generically interacting with and manipulating bit sets over types such as
//! `u128`, `[u32; 4]`, or even slices like `&[u8]`.
//!
//! To to these implementations it is possible to use bit-oriented APIs on
//! regular types, such as with arrays and vectors:
//!
//! ```
//! use bittle::Bits;
//!
//! let array: [u32; 4] = bittle::set![4, 63, 71];
//! assert!(array.iter_ones().eq([4, 63, 71]));
//! assert!(array.bit_test(63));
//!
//! let mut vector: Vec<u8> = vec![0, 1, 2, 3];
//! dbg!(vector.iter_ones().collect::<Vec<_>>());
//! assert!(vector.iter_ones().eq([8, 17, 24, 25]));
//!
//! vector.bit_set(20);
//! assert_eq!(vector, [0, 1, 18, 3]);
//! ```
//!
//! <br>
//!
//! ## Usage
//!
//! Add `bittle` as a dependency in your `Cargo.toml`:
//!
//! <br>
//!
//! ```toml
//! [dependencies]
//! bittle = "0.3.4"
//! ```
//!
//! <br>
//!
//! ## Guide
//!
//! Due to how broadly these traits are implemented, we also try and avoid using
//! names which are commonly used in other APIs, instead opting for terminology
//! such as:
//!
//! * `is_empty` becomes `is_zeros`.
//! * `test` becomes `bit_test`.
//! * `set` becomes `bit_set`.
//! * `clear` becomes `bits_clear`.
//!
//! ```rust
//! use std::mem;
//!
//! use bittle::Bits;
//!
//! let mut a = 0u64;
//!
//! assert!(a.is_zeros());
//!
//! assert!(!a.bit_test(31));
//! a.bit_set(31);
//! assert!(a.bit_test(31));
//! a.bit_clear(31);
//! assert!(!a.bit_test(31));
//! ```
//!
//! Some other interesting operations, such as [Bits::join_ones] are available,
//! allowing bitsets to act like masks over other iterators:
//!
//! ```rust
//! use bittle::Bits;
//!
//! let elements = vec![10, 48, 101];
//! let mut m = 0u128;
//!
//! m.bit_set(0);
//! assert!(m.join_ones(&elements).eq([&10]));
//! m.bit_set(2);
//! assert!(m.join_ones(&elements).eq([&10, &101]));
//! ```
//!
//! [Copy]: https://doc.rust-lang.org/std/marker/trait.Copy.html
//! [Bits::join_ones]: https://docs.rs/bittle/latest/bittle/trait.Bits.html#method.join_ones

#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![no_std]

// This library makes hard assumptions on u32 <= usize.
const _: () = assert!(core::mem::size_of::<u32>() <= core::mem::size_of::<usize>());

#[macro_use]
mod macros;

pub mod array;
pub mod number;
pub mod slice;

mod set;
pub use self::set::Set;

mod bits;
pub use self::bits::Bits;

mod owned_bits;
pub use self::owned_bits::OwnedBits;
