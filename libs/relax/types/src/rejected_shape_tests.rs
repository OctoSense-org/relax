//! Programs the check's type passes refuse, each with the error it gives: shapes that would otherwise let a
//! borrow outlive its value, read memory never written, or share a value across threads that is not `Sync`.
//! Every program is written here from scratch.
use crate::borrowck::mir_source_tests::load_source;
use crate::program::DefId;
use crate::tcx::{EvalCx, EvalState, TypingEnv};

/// The errors the check's type passes give for the crate `source`, as checked crates get them: the orphan
/// rules, well-formedness of every item, the type check of every body, and the borrow check of each body
/// whose type check passed. Each is "<item path>: <code> <message>".
fn errors(source: &str) -> Vec<String> {
    let (mut prog, tcx, user) = load_source(source, 2021, "repro");
    prog.crates[user as usize].validate = true;
    let mut out = Vec::new();
    for (d, _, e) in tcx.orphan_errors(&prog) {
        if prog.def(d).krate == user { out.push(format!("{}: {e}", prog.def_path(d))); }
    }
    for i in 0..prog.defs.len() {
        let d = DefId(i as u32);
        if prog.def(d).krate != user { continue; }
        out.extend(crate::wfcheck::obligations::check_def(&prog, &tcx, d).into_iter().map(|e| format!("{}: {e}", prog.def_path(d))));
    }
    for owner in crate::borrowck::body::owners(&prog) {
        if prog.def(owner.owner).krate != user { continue; }
        let path = prog.def_path(owner.owner);
        let body = tcx.typeck(&prog, owner.owner);
        if !body.errors.is_empty() {
            out.extend(body.errors.iter().map(|e| format!("{path}: {e}")));
            continue;
        }
        let state = EvalState::new();
        let cx = EvalCx::new(&prog, &tcx, TypingEnv::fully_monomorphized(&prog), &state);
        let v = crate::borrowck::driver::check_root(&cx, &prog, &tcx, &body, None);
        assert!(v.unchecked.is_empty(), "{path}: {:?}", v.unchecked);
        out.extend(v.errors.iter().map(|e| format!("{path}: {} {}", e.code, e.message)));
    }
    out
}

/// Whether `errors` has one with `code` for the item whose path ends in `item`.
fn has(errors: &[String], item: &str, code: &str) -> bool {
    errors.iter().any(|e| e.split_once(": ").is_some_and(|(path, rest)| (path == item || path.ends_with(&format!("::{item}"))) && rest.starts_with(code)))
}

/// `let _ = *r;` mentions the place behind `r` without using its value. Going through the `Deref` reads the
/// pointer `r`, so with `r` never initialized it is E0381, as an assignment through it would give. A mention
/// without a `Deref` reads nothing and stays accepted.
#[test]
fn a_place_mention_reads_the_pointer_it_goes_through() {
    let e = errors("
        pub fn deref() { let r: &u8; let _ = *r; }
        pub fn field() { let r: &(u8, u8); let _ = (*r).1; }
        pub fn twice() { let r: &&u8; let _ = **r; }
        pub fn matched() { let r: &u8; match *r { _ => {} } }
        pub fn tuple() { let r: &(u8, u8); let (_, _) = *r; }
        pub fn if_let() { let r: &u8; if let _ = *r {} }
        pub fn boxed() { let b: Box<u8>; let _ = *b; }
        pub fn fine(s: String) { let x: u8; let _ = x; drop(s); let _ = s; let r = &1u8; let _ = *r; }");
    for f in ["deref", "field", "twice", "matched", "tuple", "if_let", "boxed"] { assert!(has(&e, f, "E0381"), "{f}: {e:?}"); }
    assert!(!e.iter().any(|x| x.contains("fine")), "{e:?}");
}

/// `dyn TwoSuper<X, X>: Super<X>` holds through either supertrait in the type check, but the borrow check
/// (fresh regions in each position) finds the two candidates ambiguous. It must not take the ambiguity as
/// success and drop its region constraints, which would let `extend` return the short `&'a u8` it stored as
/// `&'static u8`: the goal is reported (E0283).
#[test]
fn an_ambiguous_goal_in_the_borrow_check_is_not_a_success() {
    let e = errors("
        use std::cell::Cell;
        pub trait Super<T> { fn put(&self, t: T); fn take(&self) -> T; }
        pub trait TwoSuper<A, B>: Super<A> + Super<B> {}
        pub struct Slot<X>(Cell<Option<X>>);
        impl<X> Super<X> for Slot<X> {
            fn put(&self, t: X) { self.0.set(Some(t)) }
            fn take(&self) -> X { self.0.take().unwrap() }
        }
        impl<X> TwoSuper<X, X> for Slot<X> {}
        pub fn mk<'s, X: 's>() -> Box<dyn TwoSuper<X, X> + 's> { Box::new(Slot(Cell::new(None))) }
        pub fn extend<'a>(z: &'a u8) -> &'static u8 { let cell = mk(); cell.put(z); cell.take() }");
    assert!(has(&e, "extend", ""), "{e:?}");
    assert!(!has(&e, "mk", ""), "{e:?}");
}

/// A value holding `PhantomData<*const ()>` has no interior mutability but is not `Sync`; promoting its shared
/// borrow in a fn body would make one `&'static` allocation every thread can reach, which a `static` of the type
/// is refused for. Not promoted in fn and const fn bodies (E0515); values that hold nothing that is not `Sync`
/// (`&[]`, `&None` for any `T`) stay promoted, and a const item's own lifetime-extended value stays.
#[test]
fn a_promoted_reference_to_a_value_that_is_not_sync_is_refused() {
    let e = errors(r#"
        use std::marker::PhantomData;
        pub struct NotSync(pub u8, PhantomData<*const ()>);
        pub const N: NotSync = NotSync(1, PhantomData);
        pub const CI: &NotSync = &NotSync(4, PhantomData);
        pub fn g() -> &'static NotSync { &NotSync(2, PhantomData) }
        pub fn h() -> &'static NotSync { &N }
        pub const fn k() -> &'static NotSync { &NotSync(3, PhantomData) }
        pub fn ok() -> &'static (u8, &'static str) { &(1, "x") }
        pub fn empty<T>() -> &'static [T] { &[] }
        pub fn none<T>() -> &'static Option<T> { &None }"#);
    for f in ["g", "h", "k"] { assert!(has(&e, f, "E0515"), "{f}: {e:?}"); }
    for f in ["CI", "N", "ok", "empty", "none"] { assert!(!has(&e, f, ""), "{f}: {e:?}"); }
}

/// `S<T: 'static>` built from a `&'static u8` is a covariant `S<&'s u8>`; assigning a short borrow to its field
/// shrinks `'s`, and the value would then reach `impl<T: Clone> Tr for S<T>`, whose body assumes `T: 'static`,
/// through `dyn Tr`, and a short borrow come back as `&'static u8`. A local's type must be well-formed.
#[test]
fn a_local_of_a_type_whose_bounds_fail_is_refused() {
    let e = errors("
        use std::any::Any;
        pub struct S<T: 'static>(pub T);
        pub trait Tr { fn to_any(&self) -> Box<dyn Any>; }
        impl<T: Clone> Tr for S<T> { fn to_any(&self) -> Box<dyn Any> { Box::new(self.0.clone()) } }
        pub fn extend<'x>(x: &'x u8) -> &'static u8 {
            static Z: u8 = 0;
            let mut s = S(&Z);
            s.0 = x;
            let r: &(dyn Tr + 'x) = &s;
            *r.to_any().downcast::<&'static u8>().unwrap()
        }
        pub fn fine() -> u8 { static Z: u8 = 1; let s = S(&Z); let r: &dyn Tr = &s; let _ = r.to_any(); *s.0 }");
    assert!(has(&e, "extend", ""), "{e:?}");
    assert!(!has(&e, "fine", ""), "{e:?}");
}

/// A bound that only an alias's arguments carry, `'b: 'a` from `<&'a &'b () as Trait>::Type`, is gone once the
/// alias normalizes to `()`, and a fn item used through the `Fn` traits is called without its unnormalized
/// signature being proven. The body may not assume it: implied bounds come from the normalized type, and an
/// alias contributes nothing from its arguments (lifetime may not live long enough).
#[test]
fn a_bound_only_an_alias_argument_carries_is_not_implied() {
    let e = errors("
        pub trait Trait { type Type; }
        impl<T> Trait for T { type Type = (); }
        pub fn extend<'a, 'b, T>(_: <&'a &'b () as Trait>::Type, v: &'b T) -> &'a T { v }
        pub fn fine<'a, 'b, T>(_: &'a &'b (), v: &'b T) -> &'a T { v }
        pub fn rigid<'a, X: Trait>(_: &'a X::Type, v: &'a X) -> &'a X { v }");
    assert!(has(&e, "extend", ""), "{e:?}");
    assert!(!e.iter().any(|x| x.contains("fine") || x.contains("rigid")), "{e:?}");
}
