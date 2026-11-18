// No-codegen mode (RELAX_NO_CODEGEN=1; run.sh runs it on arm64 macOS, where that mode exists): a
// module's functions taken as values -- a fn pointer, a trait object's method, the closure
// catch_unwind calls -- are its twins, reached through the sandbox's thunk table as with machine
// code, though the table holds no code there. A forged pointer still lands on a table entry: a
// twin or the trap, never host code. (--allow-unchecked-modules: the forging needs `unsafe`.)
use std::relax::Module;

const M: &str = r#"
fn triple(x: u32) -> u32 { x * 3 }
pub trait Shape { fn area(&self) -> u32; }
struct Square(u32);
impl Shape for Square { fn area(&self) -> u32 { self.0 * self.0 } }
pub fn via_value(x: u32) -> u32 { let g: fn(u32) -> u32 = triple; std::hint::black_box(g)(x) }
pub fn via_dyn(x: u32) -> u32 { let s: Box<dyn Shape> = Box::new(Square(x)); std::hint::black_box(s).area() }
pub fn via_catch(x: u32) -> u32 { std::panic::catch_unwind(|| triple(x)).unwrap_or(0) }
pub fn forged(a: u64) -> u32 { let f: fn() -> u32 = unsafe { core::mem::transmute(a as usize) }; f() }
"#;

fn host_value() -> u32 {
    0x5eed
}

#[test]
fn twin_fn_values_without_codegen() {
    let m = Module::load_source("nc_fn_values", "nc_fn_values.rs", M, &[]).unwrap();
    let value: fn(u32) -> u32 = m.get("via_value").unwrap();
    let dyn_call: fn(u32) -> u32 = m.get("via_dyn").unwrap();
    let catch: fn(u32) -> u32 = m.get("via_catch").unwrap();
    let forged: fn(u64) -> u32 = m.get("forged").unwrap();
    println!("out fn value: {:?}", std::relax::guard(1000, || value(4)));
    println!("out trait object: {:?}", std::relax::guard(1000, || dyn_call(4)));
    println!("out catch_unwind closure: {:?}", std::relax::guard(1000, || catch(4)));
    let g = std::relax::guard(1000, || forged(host_value as fn() -> u32 as u64));
    println!("out forged pointer contained: {}", g.map_or(true, |v| v != host_value()));
}
