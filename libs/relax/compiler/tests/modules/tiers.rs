// O3 keeps every guarantee a twin has below it. run.sh runs this file with O3 off (RELAX_O3=0)
// and with O3 early, waits in the second run until the twins' O3 code is installed, and requires
// both runs' lines to be equal: the result and fuel charge of each call, a Budget one unit short
// stopping it, the bounds of the module's memory (outside its arena an access ends the call or
// misses the host; inside, what was written is read back), and indirect calls (a forged pointer
// never reaches host code). (--allow-unchecked-modules: the forged accesses need `unsafe`.)
use std::relax::{guard, Budget, BudgetError, Module};

static mut SECRET: u64 = 0x1234_5678;

const M: &str = r#"
pub fn mix(n: u64) -> u64 { let mut x = 1u64; let mut i = 0; while i < n { x = x.wrapping_mul(6364136223846793005).wrapping_add(i); i += 1; } x }
pub fn fill(n: u64) -> u64 { let mut v = vec![0u8; n as usize]; for (i, b) in v.iter_mut().enumerate() { *b = i as u8; } v.iter().map(|b| *b as u64).sum() }
pub fn zero(n: u64) -> u64 { let mut a = [1u64; 64]; for x in a[..(n as usize).min(64)].iter_mut() { *x = 0; } a.iter().sum() }
pub fn table(i: u64) -> u64 { let fs: [fn(u64) -> u64; 3] = [|x| x + 1, |x| x * 2, |x| x ^ 7]; std::hint::black_box(fs)[(i % 3) as usize](i) }
pub fn own_addr() -> u64 { static mut OWN: u64 = 0; unsafe { &raw const OWN as u64 } }
pub fn read_at(a: u64) -> u64 { unsafe { *(a as *const u64) } }
pub fn write_at(a: u64, v: u64) -> u64 { unsafe { *(a as *mut u64) = v; } 1 }
pub fn call_at(a: u64) -> u64 { let f: fn() -> u64 = unsafe { core::mem::transmute(a as usize) }; f() }
"#;

fn host_value() -> u64 {
    0x5eed
}

#[test]
fn twins_keep_their_guarantees_at_o3() {
    let m = Module::load_source("tiers", "tiers.rs", M, &[]).unwrap();
    let mix: fn(u64) -> u64 = m.get("mix").unwrap();
    let fill: fn(u64) -> u64 = m.get("fill").unwrap();
    let zero: fn(u64) -> u64 = m.get("zero").unwrap();
    let table: fn(u64) -> u64 = m.get("table").unwrap();
    let own_addr: fn() -> u64 = m.get("own_addr").unwrap();
    let read_at: fn(u64) -> u64 = m.get("read_at").unwrap();
    let write_at: fn(u64, u64) -> u64 = m.get("write_at").unwrap();
    let call_at: fn(u64) -> u64 = m.get("call_at").unwrap();
    let own = own_addr();
    let warm = || {
        for _ in 0..100 {
            mix(50);
            fill(100);
            zero(10);
            table(4);
            write_at(own, 5);
            read_at(own);
        }
    };
    for _ in 0..30 {
        warm();
    }
    // with O3 on, run.sh names the JIT's O3 progress file: warm until no O3 build is pending and
    // one was installed at least
    if let Ok(progress) = std::env::var("RELAX_O3_PROGRESS") {
        loop {
            let line = std::fs::read_to_string(&progress).unwrap_or_default();
            let n: Vec<u64> = line.split_whitespace().filter_map(|x| x.parse().ok()).collect();
            if n.len() == 2 && n[0] == 0 && n[1] > 0 {
                break;
            }
            warm();
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
    let calls: [(&str, fn(u64) -> u64, u64); 4] = [("mix", mix, 1000), ("fill", fill, 3000), ("zero", zero, 40), ("table", table, 5)];
    for (name, f, arg) in calls {
        let mut budget = Budget::new(10_000_000, 1 << 24);
        let r = m.call_with(&mut budget, || f(arg));
        let fuel = budget.consumed_fuel();
        println!("out {name}({arg}): {r:?}, fuel {fuel}");
        let mut short = Budget::new(fuel - 1, 1 << 24);
        println!("out {name} one unit short stops: {}", matches!(m.call_with(&mut short, || f(arg)), Err(BudgetError::Fuel { .. })));
    }
    let secret = &raw const SECRET as u64;
    let _ = guard(1000, || write_at(secret, 1));
    println!("out host write missed the host: {}", unsafe { SECRET } == 0x1234_5678);
    println!("out host read missed the host: {}", guard(1000, || read_at(secret)).map_or(true, |v| v != 0x1234_5678));
    println!("out own memory: {:?}", guard(1000, || { write_at(own, 77); read_at(own) }));
    println!("out unmapped offset ends the call: {}", guard(1000, || read_at(0)).is_err());
    let forged = guard(1000, || call_at(host_value as fn() -> u64 as u64));
    println!("out forged pointer contained: {}", forged.map_or(true, |v| v != host_value()));
}
