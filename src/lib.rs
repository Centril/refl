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
//! You can use this to encode a subset of what GADTs allow you to in Haskell.
//!
//! This is encoded as:
//!
//! ```rust
//! use std::mem;
//! use std::marker::PhantomData;
//!
//! pub struct Id<S: ?Sized, T: ?Sized>(PhantomData<(*mut S, *mut T)>);
//!
//! pub fn refl<T: ?Sized>() -> Id<T, T> { Id(PhantomData) }
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
//! (which you can't do).
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
//! extern crate refl;
//! use refl::*;
//!
//! trait Ty { type Repr: Copy + ::std::fmt::Debug; }
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
//!     If(Box<Expr<Bool>>, Box<Expr<T>>, Box<Expr<T>>),
//! }
//!
//! fn lit<T: Ty>(lit: T::Repr) -> Box<Expr<T>> { Box::new(Expr::Lit(lit)) }
//!
//! fn eval<T: Ty>(expr: &Expr<T>) -> T::Repr {
//!     match *expr {
//!         Expr::Lit(ref val) =>
//!             *val,
//!         Expr::Add(ref refl, ref l, ref r) =>
//!             refl.cast(eval(&*l) + eval(&*r)),
//!         Expr::If(ref c, ref i, ref e) =>
//!             if eval(&*c) { eval(&*i) } else { eval(&*e) },
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

#![cfg_attr(feature = "no_std", no_std)]
#[cfg(feature = "no_std")]
extern crate core as std;

//==============================================================================
// Type equality witnesses for GADTs
//==============================================================================

use std::mem;
use std::marker::PhantomData;

/// Construct a proof witness of the fact that a
/// type is nominally equivalent to itself.
pub fn refl<T: ?Sized>() -> Id<T, T> { unsafe { unsafe_id() } }

/// A proof term that `S` and `T` are the same type (type identity).
/// This type is only every inhabited when S is nominally equivalent to T.
///
/// ## A note on variance and safety
///
/// S and T are invariant, here, this means that for two, possibly disjoint,
/// lifetimes `'a`, `'b` we can not construct an `Id<&'a T, &'b T>`. If we
/// could, which we would if we had covariance, we could define
/// the following unsafe function in safe Rust:
///
/// ```rust, ignore
/// fn transmute_lifetime<'a, 'b, T: 'a + 'b>(r: &'a T) -> &'b T {
///     refl().cast(r)
/// }
/// ```
///
/// See
/// + https://doc.rust-lang.org/nightly/nomicon/phantom-data.html
/// + https://doc.rust-lang.org/beta/nomicon/subtyping.html
/// for more information on variance.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id<S: ?Sized, T: ?Sized>(PhantomData<(*mut S, *mut T)>);

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
    pub fn sym(self) -> Id<T, S> { unsafe { unsafe_id() } }

    /// If you have proofs `Id<S, T>` and `Id<T, U>` you can conclude `Id<S, U>`
    /// since type equality is transitive.
    pub fn trans<U: ?Sized>(self, _: Id<T, U>) -> Id<S, U> {
        unsafe { unsafe_id() }
    }

    /// Casts a value of type `&S` to `&T` where `S == T`.
    ///
    /// ```rust
    /// extern crate refl;
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
    /// extern crate refl;
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
    fn default() -> Self { refl() }
}

/// We mark this unsafe since direct usage in exposed code would make
/// `.cast()` unsafe. The only safe way to construct `Id` is with `refl`.
unsafe fn unsafe_id<S: ?Sized, T: ?Sized>() -> Id<S, T> {
    Id(PhantomData)
}