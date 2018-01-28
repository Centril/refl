# `refl`

[![Build Status](https://travis-ci.org/Centril/refl.svg?branch=master)](https://travis-ci.org/Centril/refl)
[![](http://meritbadge.herokuapp.com/refl)](https://crates.io/crates/refl)

Provides a `refl` encoding which you can use to provide a proof
witness that one type is equivalent (identical) to another type.
You can use this to encode a subset of what GADTs allow you to in Haskell.

This is encoded as:
```rust
pub struct Id<S: ?Sized, T: ?Sized>(PhantomData<(*mut S, *mut T)>);

pub fn refl<T: ?Sized>() -> Id<T, T> { Id(PhantomData) }

impl<S: ?Sized, T: ?Sized> Id<S, T> {
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

    // ..
}
```

In Haskell, this type would correspond to:

```haskell
data a :~: b where
    Refl :: a :~: a
```

However, note that you must do the casting manually with `refl.cast(val)`.
Rust will not know that `S == T` by just pattern matching on `Id<S, T>`
(which you can't do).

# Example - A GADT-encoded expression type

```rust
extern crate refl;
use refl::*;

trait Ty { type Repr: Copy + ::std::fmt::Debug; }

#[derive(Debug)]
struct Int;
impl Ty for Int { type Repr = usize; }

#[derive(Debug)]
struct Bool;
impl Ty for Bool { type Repr = bool; }

#[derive(Debug)]
enum Expr<T: Ty> {
    Lit(T::Repr),
    Add(Id<usize, T::Repr>, Box<Expr<Int>>, Box<Expr<Int>>),
    If(Box<Expr<Bool>>, Box<Expr<T>>, Box<Expr<T>>),
}

fn lit<T: Ty>(lit: T::Repr) -> Box<Expr<T>> { Box::new(Expr::Lit(lit)) }

fn eval<T: Ty>(expr: &Expr<T>) -> T::Repr {
    match *expr {
        Expr::Lit(ref val) =>
            *val,
        Expr::Add(ref refl, ref l, ref r) =>
            refl.cast(eval(&*l) + eval(&*r)),
        Expr::If(ref c, ref i, ref e) =>
            if eval(&*c) { eval(&*i) } else { eval(&*e) },
    }
}

fn main() {
    let expr: Expr<Int> =
        Expr::If(
            Box::new(Expr::Lit(false)),
            Box::new(Expr::Lit(1)),
            Box::new(Expr::Add(
                refl(),
                Box::new(Expr::Lit(2)),
                Box::new(Expr::Lit(3)),
            ))
        );

    assert_eq!(eval(&expr), 5);
}
```

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
