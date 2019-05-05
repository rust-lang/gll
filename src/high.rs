//! Utilities for emulating HKTs (over lifetimes) in Rust.

use std::mem;
use std::ops::{Deref, DerefMut};

/// Type lambda application, with a lifetime.
pub trait ApplyL<'a> {
    type Out;
}

/// Type lambda taking a lifetime, i.e. `Lifetime -> Type`.
pub trait LambdaL: for<'a> ApplyL<'a> {}

impl<T: for<'a> ApplyL<'a>> LambdaL for T {}

// HACK(eddyb) work around `macro_rules` not being `use`-able.
pub use crate::__high_type_lambda as type_lambda;

/// Define a new "type lambda" (over a lifetime).
///
/// For example, `type_lambda!(type<'a> X = Y<Z<'a>>;)` defines
/// a `struct X {...}` that implements `ApplyL`, such that
/// `for<'a> <X as ApplyL<'a>>::Out = Y<Z<'a>>` holds.
#[macro_export]
macro_rules! __high_type_lambda {
    ($($vis:vis type<$lt:lifetime> $name:ident $(<$($T:ident $(: $bound:path)*),*>)* = $ty:ty;)+) => {
        $($vis struct $name $(<$($T $(: $bound)*),*>)* {
            _marker: ::std::marker::PhantomData<($($($T),*)*)>,
        }
        impl<$lt, $($($T $(: $bound)*),*)*> $crate::high::ApplyL<$lt>
            for $name $(<$($T),*>)*
        {
            type Out = $ty;
        })+
    }
}

type_lambda! {
    pub type<'a> PairL<A: LambdaL, B: LambdaL> =
        (<A as ApplyL<'a>>::Out, <B as ApplyL<'a>>::Out);
}

// HACK(eddyb) work around projection limitations with a newtype
// FIXME(#52812) replace with `&'a <T as ApplyL<'b>>::Out`
pub struct RefApplyL<'a, 'b, T: LambdaL>(&'a <T as ApplyL<'b>>::Out);

impl<'a, T: LambdaL> Deref for RefApplyL<'_, 'a, T> {
    type Target = <T as ApplyL<'a>>::Out;
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

// HACK(eddyb) work around projection limitations with a newtype
// FIXME(#52812) replace with `&'a mut <T as ApplyL<'b>>::Out`
pub struct RefMutApplyL<'a, 'b, T: LambdaL>(&'a mut <T as ApplyL<'b>>::Out);

impl<'b, T: LambdaL> Deref for RefMutApplyL<'_, 'b, T> {
    type Target = <T as ApplyL<'b>>::Out;
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'b, T: LambdaL> DerefMut for RefMutApplyL<'_, 'b, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

/// Proof token for erasable lifetimes (soundly replaceable with existentials).
/// That is, the lifetime is not used in references that borrow outside
/// data, but rather only self-contained (e.g. `indexing` or `owning_ref`).
#[derive(Copy, Clone)]
pub struct ErasableL<'a> {
    _marker: ::std::marker::PhantomData<&'a mut &'a ()>,
}

impl ErasableL<'_> {
    /// Trivial proof that `'static` is erasable (it's always valid).
    pub const STATIC: ErasableL<'static> = ErasableL {
        _marker: ::std::marker::PhantomData,
    };

    /// Enter an `indexing::scope`, where the closure also receives a proof that
    /// the generative lifetime is erasable (it doesn't come from a borrow).
    pub fn indexing_scope<A: ::indexing::container_traits::Trustworthy, R>(
        a: A,
        f: impl for<'id> FnOnce(ErasableL<'id>, ::indexing::Container<'id, A>) -> R,
    ) -> R {
        ::indexing::scope(a, |container| {
            f(
                ErasableL {
                    _marker: ::std::marker::PhantomData,
                },
                container,
            )
        })
    }
}

/// Existential over a lifetime, i.e. `exists 'a.T('a)`.
pub struct ExistsL<T: LambdaL>(<T as ApplyL<'static>>::Out);

impl<T: LambdaL> ExistsL<T> {
    /// Erase the lifetime `'a` from the value's type and wrap it in `ExistsL`.
    /// This requires a proof that `'a` is erasable at all (see `ErasableL`).
    /// To access the value later, use `unpack`, `unpack_ref` or `unpack_mut`.
    pub fn pack<'a>(_: ErasableL<'a>, value: <T as ApplyL<'a>>::Out) -> Self {
        let erased = unsafe { mem::transmute_copy(&value) };
        mem::forget(value);
        ExistsL(erased)
    }

    /// Provide owned access to the value, with the original lifetime replaced
    /// by a generative lifetime, so that the closure can't assume equality
    /// to any other specific lifetime (thanks to lifetime parametricity).
    pub fn unpack<R>(
        self,
        f: impl for<'a> FnOnce(ErasableL<'a>, <T as ApplyL<'a>>::Out) -> R,
    ) -> R {
        let skolem = unsafe { mem::transmute_copy(&self.0) };
        mem::forget(self);
        f(
            ErasableL {
                _marker: ::std::marker::PhantomData,
            },
            skolem,
        )
    }

    /// Provide shared access to the value, with the original lifetime replaced
    /// by a generative lifetime, so that the closure can't assume equality
    /// to any other specific lifetime (thanks to lifetime parametricity).
    pub fn unpack_ref<R>(
        &self,
        f: impl for<'a, 'b> FnOnce(ErasableL<'b>, RefApplyL<'a, 'b, T>) -> R,
    ) -> R {
        f(
            ErasableL {
                _marker: ::std::marker::PhantomData,
            },
            RefApplyL(unsafe { &*(&self.0 as *const _ as *const _) }),
        )
    }

    /// Provide mutable access to the value, with the original lifetime replaced
    /// by a generative lifetime, so that the closure can't assume equality
    /// to any other specific lifetime (thanks to lifetime parametricity).
    pub fn unpack_mut<R>(
        &mut self,
        f: impl for<'a, 'b> FnOnce(ErasableL<'b>, RefMutApplyL<'a, 'b, T>) -> R,
    ) -> R {
        f(
            ErasableL {
                _marker: ::std::marker::PhantomData,
            },
            RefMutApplyL(unsafe { &mut *(&mut self.0 as *mut _ as *mut _) }),
        )
    }
}
