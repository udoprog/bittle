//! [<img alt="github" src="https://img.shields.io/badge/github-udoprog/bittle-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/bittle)
//! [<img alt="crates.io" src="https://img.shields.io/crates/v/bittle.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/bittle)
//! [<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-bittle-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/bittle)
//! [<img alt="build status" src="https://img.shields.io/github/workflow/status/udoprog/bittle/CI/main?style=for-the-badge" height="20">](https://github.com/udoprog/bittle/actions?query=branch%3Amain)
//!
//! Zero-cost bitsets over native Rust types.
//!
//! The name `bittle` comes from `bit` and `little`. Small bitsets!
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
//! bittle = "0.4.1"
//! ```
//!
//! <br>
//!
//! ## Guide
//!
//! This crate defines the [`Bits`], [`BitsMut`], and [`BitsOwned`] traits which
//! allows for generically interacting bit sets over existing Rust types such as
//! `u32`, `[u32; 4]`, or `&[u32]`:
//!
//! ```
//! use bittle::Bits;
//!
//! let array: [u32; 4] = [0, 1, 2, 3];
//! assert!(array.iter_ones().eq([63, 94, 126, 127]));
//!
//! let n = 0b10001000_00000000_00000000_00000000u32;
//! assert!(n.iter_ones().eq([0, 4]));
//!
//! let array_of_arrays: [[u8; 4]; 2] = [[8, 0, 0, 0], [0, 0, 128, 0]];
//! assert!(array_of_arrays.iter_ones().eq([4, 48]));
//!
//! let mut vec: Vec<u32> = vec![0, 1, 2, 3];
//! assert!(vec.iter_ones().eq([63, 94, 126, 127]));
//! ```
//!
//! <br>
//!
//! We provide the [`set!`] macro, which is a zero-cost convenience method of
//! constructing primitive forms of bit sets:
//!
//! ```
//! use bittle::Bits;
//!
//! let array: [u32; 4] = bittle::set![63, 94, 126, 127];
//! assert!(array.iter_ones().eq([63, 94, 126, 127]));
//!
//! let array_of_arrays: [[u8; 4]; 2] = bittle::set![4, 48];
//! assert!(array_of_arrays.iter_ones().eq([4, 48]));
//!
//! let n: u32 = bittle::set![0, 4];
//! assert!(n.iter_ones().eq([0, 4]));
//! ```
//!
//! <br>
//!
//! Since a vector is not a primitive bit set, it could instead make use of
//! [`BitsMut`] directly:
//!
//! ```
//! use bittle::{Bits, BitsMut};
//!
//! let mut vec: Vec<u32> = vec![0u32; 4];
//! vec.set_bit(63);
//! vec.set_bit(94);
//! vec.set_bit(126);
//! vec.set_bit(127);
//! assert!(vec.iter_ones().eq([63, 94, 126, 127]));
//! ```
//!
//! <br>
//!
//! Due to how broadly these traits are implemented, we also try to avoid using
//! names which are commonly used in other APIs, instead opt for bit-specific
//! terminology such as:
//!
//! * Something like `is_empty` becomes `all_zeros` - since with bits you're
//!   thinking about "ones and zeros".
//! * Testing if a bit is set is `test_bit`, or in general adding the `*_bit`
//!   suffix to operations over individual bits.
//! * Clearing all bits becomes `clear_bits`, or in general adding the `*_bits`
//!   suffix when operating over *all* bits.
//!
//! ```rust
//! use bittle::{Bits, BitsMut};
//!
//! let mut set = [0u16; 2];
//!
//! set.set_bit(15);
//! assert!(set.test_bit(15));
//!
//! set.union_assign(&bittle::set![31, 7]);
//! assert!(set.test_bit(31) && set.test_bit(7));
//!
//! set.clear_bit(31);
//! assert!(!set.test_bit(31));
//!
//! set.clear_bits();
//! assert!(set.all_zeros());
//! ```
//!
//! <br>
//!
//! Some other interesting operations, such as [`Bits::join_ones`] are available,
//! allowing bitsets to act like masks over other iterators:
//!
//! ```rust
//! use bittle::{Bits, BitsMut};
//!
//! let elements = vec![10, 48, 101];
//! let mut m = 0u128;
//!
//! m.set_bit(0);
//! assert!(m.join_ones(&elements).eq([&10]));
//! m.set_bit(2);
//! assert!(m.join_ones(&elements).eq([&10, &101]));
//! ```
//!
//! <br>
//!
//! [`set!`]: https://docs.rs/bittle/latest/bittle/macro.set.html
//! [`Copy`]: https://doc.rust-lang.org/std/marker/trait.Copy.html
//! [`Bits`]: https://docs.rs/bittle/latest/bittle/trait.Bits.html
//! [`BitsMut`]: https://docs.rs/bittle/latest/bittle/trait.BitsMut.html
//! [`BitsOwned`]: https://docs.rs/bittle/latest/bittle/trait.BitsOwned.html
//! [`Bits::join_ones`]: https://docs.rs/bittle/latest/bittle/trait.Bits.html#method.join_ones

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

mod bits_mut;
pub use self::bits_mut::BitsMut;

mod bits_owned;
pub use self::bits_owned::BitsOwned;

pub mod prelude {
    //! Prelude use to conveniently import all relevant bits-oriented traits.
    pub use crate::{Bits, BitsMut, BitsOwned};
}
