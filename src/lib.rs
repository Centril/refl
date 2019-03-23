//-
// Copyright 2018 Mazdak Farrokhzad
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Provides a `refl` encoding which you can use to provide a proof
//! witness that one type is equivalent (identical) to another type.
//! This can be used to encode a subset of what GADTs allow you to in Haskell.
//!
//! This is encoded as:
//!
//! ```rust
//! use core::mem;
//! use core::marker::PhantomData;
//!
//! pub struct Id<S: ?Sized, T: ?Sized>(PhantomData<(fn(S) -> S, fn(T) -> T)>);
//!
//! impl<T: ?Sized> Id<T, T> { pub const REFL: Self = Id(PhantomData); }
//!
//! pub fn refl<T: ?Sized>() -> Id<T, T> { Id::REFL }
//!
//! impl<S: ?Sized, T: ?Sized> Id<S, T> {
//!     /// Casts a value of type `S` to `T`.
//!     ///
//!     /// This is safe because the `Id` type is always guaranteed to
//!     /// only be inhabited by `Id<T, T>` types by construction.
//!     pub fn cast(self, value: S) -> T where S: Sized, T: Sized {
//!         unsafe {
//!             // Transmute the value;
//!             // This is safe since we know by construction that
//!             // S == T (including lifetime invariance) always holds.
//!             let cast_value = mem::transmute_copy(&value);
//!
//!             // Forget the value;
//!             // otherwise the destructor of S would be run.
//!             mem::forget(value);
//!
//!             cast_value
//!         }
//!     }
//!
//!     // ..
//! }
//! ```
//!
//! In Haskell, the `Id<A, B>` type corresponds to:
//!
//! ```haskell
//! data a :~: b where
//!     Refl :: a :~: a
//! ```
//!
//! However, note that you must do the casting manually with `refl.cast(val)`.
//! Rust will not know that `S == T` by just pattern matching on `Id<S, T>`
//! (which you cannot do).
//!
//! # Limitations
//!
//! Please note that Rust has no concept of higher kinded types (HKTs) and so
//! we can not provide the general transformation `F<S> -> F<T>` given that
//! `S == T`. With the introduction of generic associated types (GATs), it
//! may be possible to introduce more transformations.
//!
//! # Example - A GADT-encoded expression type
//!
//! ```rust
//! use refl::*;
//!
//! trait Ty { type Repr: Copy + core::fmt::Debug; }
//!
//! #[derive(Debug)]
//! struct Int;
//! impl Ty for Int { type Repr = usize; }
//!
//! #[derive(Debug)]
//! struct Bool;
//! impl Ty for Bool { type Repr = bool; }
//!
//! #[derive(Debug)]
//! enum Expr<T: Ty> {
//!     Lit(T::Repr),
//!     Add(Id<usize, T::Repr>, Box<Expr<Int>>, Box<Expr<Int>>),
//!     If(Box<Expr<Bool>>, Box<Self>, Box<Self>),
//! }
//!
//! fn eval<T: Ty>(expr: &Expr<T>) -> T::Repr {
//!     match expr {
//!         Expr::Lit(val) => *val,
//!         Expr::Add(refl, l, r) => refl.cast(eval(l) + eval(r)),
//!         Expr::If(c, i, e) => if eval(c) { eval(i) } else { eval(e) },
//!     }
//! }
//!
//! fn main() {
//!     let expr: Expr<Int> =
//!         Expr::If(
//!             Box::new(Expr::Lit(false)),
//!             Box::new(Expr::Lit(1)),
//!             Box::new(Expr::Add(
//!                 refl(),
//!                 Box::new(Expr::Lit(2)),
//!                 Box::new(Expr::Lit(3)),
//!             ))
//!         );
//!
//!     assert_eq!(eval(&expr), 5);
//! }
//! ```

//==============================================================================
// Type equality witnesses for GADTs
//==============================================================================

use core::{cmp, fmt, hash, mem, marker::PhantomData};

/// Construct a proof witness of the fact that a type is equivalent to itself.
///
/// This is equivalent to `Id::REFL`.
pub const fn refl<T: ?Sized>() -> Id<T, T> { Id::REFL }

impl<T: ?Sized> Id<T, T> {
    /// A proof witness of the fact that a type is equivalent to itself.
    ///
    /// This is equivalent to `refl()`.
    pub const REFL: Self = Self(PhantomData);
}

/// A proof term that `S` and `T` are the same type (type identity).
/// This type is only ever inhabited when S is nominally equivalent to T.
///
/// ## A note on variance and safety
///
/// S and T are invariant here. This means that for two, possibly disjoint,
/// lifetimes `'a`, `'b` we cannot construct an `Id<&'a T, &'b T>`. If we
/// could, which we would if we had covariance, we could define
/// the following unsound function in safe Rust:
///
/// ```ignore
/// fn transmute_lifetime<'a, 'b, T: 'a + 'b>(r: &'a T) -> &'b T {
///     refl().cast(r)
/// }
/// ```
///
/// See
///
/// - <https://doc.rust-lang.org/nightly/nomicon/phantom-data.html>
/// - <https://doc.rust-lang.org/beta/nomicon/subtyping.html>
///
/// for more information on variance.
pub struct Id<S: ?Sized, T: ?Sized>(PhantomData<(fn(S) -> S, fn(T) -> T)>);

impl<S: ?Sized, T: ?Sized> Id<S, T> {
    //==========================================================================
    // Reflexivity, Symmetry, Transivity:
    //==========================================================================

    /// Casts a value of type `S` to `T`.
    ///
    /// This is safe because the `Id` type is always guaranteed to
    /// only be inhabited by `Id<T, T>` types by construction.
    pub fn cast(self, value: S) -> T where S: Sized, T: Sized {
        unsafe {
            // Transmute the value;
            // This is safe since we know by construction that
            // S == T (including lifetime invariance) always holds.
            let cast_value = mem::transmute_copy(&value);

            // Forget the value;
            // otherwise the destructor of S would be run.
            mem::forget(value);

            cast_value
        }
    }

    /// Converts `Id<S, T>` into `Id<T, S>` since type equality is symmetric.
    pub fn sym(self) -> Id<T, S> { Self(PhantomData) }

    /// If you have proofs `Id<S, T>` and `Id<T, U>` you can conclude `Id<S, U>`
    /// since type equality is transitive.
    pub fn trans<U: ?Sized>(self, _: Id<T, U>) -> Id<S, U> { Self(PhantomData) }

    /// Casts a value of type `&S` to `&T` where `S == T`.
    ///
    /// ```rust
    /// use refl::*;
    ///
    /// fn main() {
    ///     let x: Box<u8> = Box::new(1);
    ///     let refl: Id<Box<u8>, Box<u8>> = refl();
    ///     assert_eq!(&x, refl.cast_ref(&x));
    /// }
    /// ```
    pub fn cast_ref<'a>(self, value: &'a S) -> &'a T {
        unsafe {
            // Transmute the value;
            // This is safe since we know by construction that
            // S == T (including lifetime invariance) always holds.
            mem::transmute_copy(&value)

            // mem::forget not needed since &'a S has a trivial destructor.
        }
    }

    /// Casts a value of type `&S` to `&T` where `S == T`.
    /// 
    /// ```rust
    /// use refl::*;
    ///
    /// fn main() {
    ///     let mut x: Box<u8> = Box::new(1);
    ///     let refl: Id<Box<u8>, Box<u8>> = refl();
    ///     **refl.cast_ref_mut(&mut x) += 1;
    ///     assert_eq!(*x, 2);
    /// }
    /// ```
    pub fn cast_ref_mut<'a>(self, value: &'a mut S) -> &'a mut T {
        unsafe {
            // Transmute the value;
            // This is safe since we know by construction that
            // S == T (including lifetime invariance) always holds.
            mem::transmute_copy(&value)

            // mem::forget not needed since &'a mut S has a trivial destructor.
        }
    }

    // We could define it for other functors,
    // but we can't do it for all functors...
}

impl<X: ?Sized> Default for Id<X, X> {
    fn default() -> Self { Self::REFL }
}

impl<S: ?Sized, T: ?Sized> Copy for Id<S, T> {}

impl<S: ?Sized, T: ?Sized> Clone for Id<S, T> {
    fn clone(&self) -> Self { Self(PhantomData) }
    fn clone_from(&mut self, _: &Self) {}
}

impl<S: ?Sized, T: ?Sized> fmt::Debug for Id<S, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("Id(_)")
    }
}

impl<S: ?Sized, T: ?Sized> hash::Hash for Id<S, T> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<S: ?Sized, T: ?Sized> cmp::PartialEq for Id<S, T> {
    fn eq(&self, _: &Self) -> bool { true }
    fn ne(&self, _: &Self) -> bool { false }
}

impl<S: ?Sized, T: ?Sized> cmp::Eq for Id<S, T> {}

impl<S: ?Sized, T: ?Sized> cmp::PartialOrd for Id<S, T> {
    fn partial_cmp(&self, _: &Self) -> Option<cmp::Ordering> {
        Some(cmp::Ordering::Equal)
    }
}

impl<S: ?Sized, T: ?Sized> cmp::Ord for Id<S, T> {
    fn cmp(&self, _other: &Self) -> cmp::Ordering {
        cmp::Ordering::Equal
    }
}

#[cfg(test)]
#[test]
fn checks() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Id<*mut u8, *mut u8>>();
}
