# VerifiedJS — Failing Tests

Track failing tests with minimal repros. Use `--run=<IL>` to bisect.

Format:
```
### test_name
**Input**: `code`
**Expected**: output
**Actual**: output
**Bisection**: fails at <IL> level
**Status**: OPEN | FIXED
```

---

### multiple_functions.js — FIXED 2026-03-20T15:51
**Fix**: Proof agent replaced hardcoded __rt_call with console.log detection + __rt_printValue helper + direct function call optimization.
**Status**: FIXED

### multi_func_log.js — FIXED 2026-03-20T15:51
**Fix**: Same console.log fix as multiple_functions.
**Status**: FIXED

### while_loop.js — FIXED 2026-03-20T15:51
**Fix**: Proof agent fixed while loop block to push undefined after block (stack balance), removed start section (double-execution), added proper console.log output.
**Status**: FIXED

### while_loop_log.js — FIXED 2026-03-20T15:51
**Fix**: Same while loop + console.log fix.
**Status**: FIXED

### nested_control.js — FIXED 2026-03-20T15:51
**Fix**: Same fixes (while loop + console.log + if_ label fix from wasmspec).
**Status**: FIXED

---

### switch_case.js — FIXED 2026-03-20T17:04
**Fix**: jsspec implemented switch/case semantics; wasmspec/proof fixed lowering.
**Status**: FIXED

### try_catch.js — FIXED 2026-03-20T17:04
**Fix**: jsspec implemented try/catch/finally Core semantics (ECMA-262 §13.15).
**Status**: FIXED

### try_finally.js — FIXED 2026-03-20T17:04
**Fix**: jsspec fixed finally block semantics — runs body then finally correctly.
**Status**: FIXED

### typeof_test.js — FIXED 2026-03-20T17:04
**Fix**: jsspec implemented typeof operator Core semantics (ECMA-262 §12.5.6).
**Status**: FIXED

---

### for_in.js — NEW 2026-03-20T17:04
**Input**: `for (let k in obj) { console.log(k) }`
**Expected**: `a\nb\nc`
**Actual**: (empty output)
**Bisection**: Core semantics implemented but Elaborate.lean returns undef for for-in (not elaborated)
**Status**: OPEN

### for_of.js — NEW 2026-03-20T17:04
**Input**: `for (let x of arr) { console.log(x) }`
**Expected**: `10\n20\n30`
**Actual**: (empty output)
**Bisection**: Core semantics implemented but Elaborate.lean returns undef for for-of (not elaborated)
**Status**: OPEN

### new_obj.js — NEW 2026-03-20T17:04
**Input**: `new Object()` / `typeof new Object()`
**Expected**: `object`
**Actual**: Wasm runtime trap — "invalid conversion to integer"
**Bisection**: Core semantics implemented but Wasm lowering for newObj not complete
**Status**: OPEN

### set_prop.js — NEW 2026-03-20T17:04
**Input**: `obj.x = 42; obj.y = "hello"`
**Expected**: `42\nhello`
**Actual**: Wasm runtime trap — "invalid conversion to integer"
**Bisection**: Core semantics implemented but Wasm lowering for setProp not complete
**Status**: OPEN

---

### arrow_func.js — NEW 2026-03-20T17:23
**Input**: Arrow function definition and invocation
**Expected**: `15\n9`
**Actual**: Wasm runtime trap
**Bisection**: Arrow function lowering to Wasm incomplete
**Status**: OPEN

### bitwise_ops.js — NEW 2026-03-20T17:23
**Input**: Bitwise AND, OR, XOR operations
**Expected**: `0\n7\n6`
**Actual**: `10\n7\n8` (wrong results for AND and XOR)
**Bisection**: Bitwise operator stubs in Core semantics produce incorrect values
**Status**: OPEN

### nullish_coalesce.js — NEW 2026-03-20T17:23
**Input**: `x ?? default` with null/undefined values
**Expected**: `42\ndefault`
**Actual**: First value correct, then wasm runtime trap on null/undefined
**Bisection**: Null/undefined handling incomplete in Wasm lowering
**Status**: OPEN

### template_lit.js — REMOVED 2026-03-20T17:30
**Status**: REMOVED (test file deleted by jsspec)

---

## BUILD BROKEN — 2026-03-20T17:30 — FIXED 2026-03-20T17:51

### ANF/Semantics.lean termination proof failure — FIXED
**Cause**: wasmspec initially used `sizeOf s.expr` which didn't work. Fixed by using `Expr.depth` measure with proper depth functions and theorems.
**Fix**: wasmspec rewrote ANF.step? and Flat.step? with `Expr.depth` termination, including mutual depth functions and helper theorems.
**Status**: FIXED

### arrow_func.js, bitwise_ops.js, nullish_coalesce.js — REMOVED 2026-03-20T17:30
**Status**: REMOVED (test files deleted by jsspec, replaced with new tests)

---

### new_obj.js — FIXED 2026-03-20T17:51
**Fix**: Proof agent implemented __rt_construct (heap allocator for objects).
**Status**: FIXED

### set_prop.js — FIXED 2026-03-20T17:51
**Fix**: Proof agent implemented __rt_setProp (property storage in linear memory).
**Status**: FIXED

---

### fibonacci.js — FIXED 2026-03-20T19:08
**Fix**: Proof agent implemented selfRef for recursive calls, function index offset for correct Wasm function indices.
**Status**: FIXED

### logical_ops.js — FIXED 2026-03-20T19:08
**Fix**: Proof agent implemented __rt_logicalAnd and __rt_logicalOr runtime functions with JS short-circuit semantics.
**Status**: FIXED

### string_concat.js — NEW 2026-03-20T17:30
**Input**: String concatenation with `+`
**Expected**: `hello 42\ntrue!\ncount: 5`
**Actual**: `undefined` for all
**Bisection**: Wasm lowering — string concatenation in binaryAdd not implemented
**Status**: OPEN

---

## BUILD BROKEN — 2026-03-20T22:05

### ANFConvertCorrect.lean compilation errors
**Cause**: Proof agent restructured ANFConvertCorrect.lean with observable trace infrastructure. Two simp proofs fail: `observableTrace_log` and `observableTrace_error` — `simp [observableTrace, List.filter]` cannot reduce `Core.TraceEvent.log s != Core.TraceEvent.silent` because simp doesn't unfold the derived BEq instance.
**Fix**: Add `BNe.bne, BEq.beq` to the simp set in both theorems.
**Impact**: Proof module fails to build. E2E tests still work (don't depend on Proofs module). `lake build` reports FAIL.
**Status**: OPEN — proof agent instructed to fix
