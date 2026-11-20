#!/bin/bash
# usage: run.sh [<makepad binary>] (none: builds this checkout's host makepad): the test
# dependency check keys a crate's verdict by its own text and its dependencies' interfaces (M51).
# A body edit in tdk-base checks tdk-base again, not tdk-mid above it; an interface edit checks both.
# Never stale: in each case below the crates are clean as written, and one change that leaves the
# interface text as it was (a static a const reads, a position a const reads, an input a macro
# reads) makes tdk-mid's `sized` fail. The run after it must report that error, not tdk-mid's
# stored verdict.
H=$(cd "$(dirname "$0")" && pwd)
if [ $# -ge 1 ]; then J=$1; else
  ROOT=$(cd "$H/../../../../.." && pwd)
  cargo build --profile host -q --manifest-path "$ROOT/Cargo.toml" -p makepad-run --bin makepad || exit 1
  J=${CARGO_TARGET_DIR:-$ROOT/target}/host/makepad
fi
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
cp -R "$H/." "$W/"
unset RELAX_STD RELAX_CACHE RELAX_CACHE_DIR
export RELAX_VERBOSE=1
# "<selected> <stored clean>" of one run
counts() {
  local out
  out=$(cd "$W" && "$1" test test-dep-keys 2>&1)
  echo "$out" | grep -q '^test t::uses_mid \.\.\. ok' || { echo "$out" | tail -20 >&2; echo "x x"; return; }
  echo "$out" | sed -n 's/.*test dependency check: \([0-9]*\) crates selected, \([0-9]*\) stored clean.*/\1 \2/p' | tail -1
}
cold=$(counts "$J")
cp "$W/edits/body.rs" "$W/base/src/lib.rs"
body=$(counts "$J")
cp "$W/edits/iface.rs" "$W/base/src/lib.rs"
iface=$(counts "$J")
echo "cold: $cold; body edit: $body; interface edit: $iface (selected, stored clean)"
bad=""
if [ "$cold" != "2 0" ] || [ "$body" != "2 1" ] || [ "$iface" != "2 0" ]; then bad=" keys (want 2 0, 2 1, 2 0)"; fi

# a run's outcome: ok, or mid (the dependency check reported tdk-mid's error)
outcome() {
  local out
  out=$(cd "$W" && "$J" test test-dep-keys 2>&1)
  if echo "$out" | grep -q 'could not compile `tdk-mid`'; then echo mid
  elif echo "$out" | grep -q '^test t::uses_mid \.\.\. ok'; then echo ok
  else echo "$out" | tail -20 >&2; echo x; fi
}
# file $1 of the copy holds $2
put() { mkdir -p "$(dirname "$W/$1")"; printf '%s\n' "$2" > "$W/$1"; }
# case <name> <change>: a clean run as the crates are written, then the change, then a run that
# reports tdk-mid's error
case_() {
  local a b
  a=$(outcome)
  eval "$2"
  b=$(outcome)
  echo "$1: $a, then $b"
  if [ "$a" != ok ] || [ "$b" != mid ]; then bad="$bad $1"; fi
}
MID='pub fn mid_value() -> u32 {
    tdk_base::base_value() + 1
}

// no test calls it: the dependency check alone checks it
pub fn sized() -> [u8; 3] {
    [0u8; tdk_base::C]
}'
put mid/src/lib.rs "$MID"

# the statics' initializers a const reads: two statics trading them
put base/src/lib.rs 'pub fn base_value() -> u32 { 1 }
static S: usize = 3;
pub static T: usize = 4;
pub const C: usize = S;'
case_ static "sed -i.x -e 's/S: usize = 3;/S: usize = 9;/' -e 's/T: usize = 4;/T: usize = 3;/' -e 's/S: usize = 9;/S: usize = 4;/' '$W/base/src/lib.rs'"

# the line a const is written on (caller_location), after a body that gains a line
put base/src/lib.rs 'pub fn base_value() -> u32 { 1 }
// C is the line it is written on
pub const C: usize = core::panic::Location::caller().line() as usize;'
case_ caller "sed -i.x 's/{ 1 }/{\\
    1 }/' '$W/base/src/lib.rs'"

# the same through a #[track_caller] const fn: the const that calls it names no position
put base/src/lib.rs '#[track_caller]
pub const fn line_here() -> usize { core::panic::Location::caller().line() as usize }
pub fn base_value() -> u32 { 1 }
pub const C: usize = line_here() - 1;'
case_ track_caller "sed -i.x 's/{ 1 }/{\\
    1 }/' '$W/base/src/lib.rs'"

# line!()
put base/src/lib.rs 'pub fn base_value() -> u32 { 1 }
// C is the line it is written on
pub const C: usize = line!() as usize;'
case_ line "sed -i.x 's/{ 1 }/{\\
    1 }/' '$W/base/src/lib.rs'"

# a file a const includes
put base/src/data.txt abc
put base/src/lib.rs 'pub fn base_value() -> u32 { 1 }
pub const C: usize = include_str!("data.txt").len() - 1;'
case_ include_str "put base/src/data.txt abcd"

# an environment variable a const reads
export TDK_TEXT=abc
put base/src/lib.rs 'pub fn base_value() -> u32 { 1 }
pub const C: usize = env!("TDK_TEXT").len();'
case_ env "export TDK_TEXT=abcd"

# a file tdk-mid's own body includes (its type is the file's length)
put base/src/lib.rs 'pub fn base_value() -> u32 { 1 }
pub const C: usize = 3;'
put mid/src/own.bin abc
put mid/src/lib.rs "$MID
pub fn own() -> [u8; 4] {
    *include_bytes!(\"own.bin\")
}"
case_ include_bytes "printf abc > '$W/mid/src/own.bin'"

if [ -z "$bad" ]; then echo "test_dep_keys: ok"
else echo "test_dep_keys: FAILED:$bad"; exit 1; fi
