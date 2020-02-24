## 0.2.1

- A plugged rustc bug would stop the crate from compiling.
  This has been fixed in this release.

## 0.2.0

- Migrated to edition 2018. Rust 1.32 is now required.
- `refl` is now a `const fn`.
- `#![no_std]` is unconditionally applied and requires cargo features.

## 0.1.3

- Relaxed bounds on various implemented traits for `Id<A, B>`.

## 0.1.2

## New additions

- Added associated constant `Id::REFL` for const contexts.

## Bug fixes

- Fixes in documentation rendering.

## 0.1.1

- Added bounds `Sync` and `Send` on `Id<S, T>`

## 0.1.0

- Initial version.
