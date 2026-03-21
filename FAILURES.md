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

## BUILD BROKEN — 2026-03-20T22:05 — PARTIALLY ADDRESSED

### ANFConvertCorrect.lean compilation errors — STILL OPEN
**Cause**: `BNe.bne` removed in Lean 4.29. Proof agent's `simp [BNe.bne, BEq.beq]` proofs fail.
**Fix**: Replace observableTrace_silent/log/error proofs with `rfl`. Fix line 111 `congr 1` type mismatch.
**Status**: OPEN — proof agent has exact fix code in prompt

### EmitCorrect.lean line 32 — NEW 2026-03-21T00:01
**Cause**: `emit_single_import` proof — `simp_all [Pure.pure]` doesn't solve the goal after `split`.
**Fix**: Proof agent needs to add more lemmas to the simp set or use a different tactic.
**Status**: OPEN — proof agent

## BUILD BROKEN — 2026-03-20T23:35 — FIXED 2026-03-21T00:06

### Wasm/Semantics.lean — FIXED by wasmspec
**Fix**: wasmspec fixed injection tactic, BlockType.val, and struct syntax errors.
**Status**: FIXED

---

## New E2E Failures — 2026-03-21T01:05

### array_push_sim.js — NEW
**Expected**: `100` **Actual**: `undefined`
**Status**: OPEN — likely missing Array.push runtime support

### bitwise_ops.js — KNOWN BUG (re-added test)
**Expected**: `7` **Actual**: `8` (bitwise XOR produces wrong result)
**Status**: OPEN

### counter_closure.js — NEW
**Expected**: `1` **Actual**: wasm runtime error (failed to run)
**Status**: OPEN — likely indirect call type mismatch in closure handling

### iife.js — NEW
**Expected**: `42` **Actual**: `undefined`
**Status**: OPEN — IIFE (immediately invoked function expression) not handled

### modulo_ops.js — NEW
**Expected**: `1` **Actual**: `3` (wrong modulo result)
**Status**: OPEN — modulo operator producing incorrect values

### mutual_recursion.js — NEW
**Expected**: `true` **Actual**: wasm runtime error (failed to run)
**Status**: OPEN — mutual recursion not supported in function lowering

### nested_try_catch.js — NEW
**Expected**: `inner` **Actual**: wasm compilation error
**Status**: OPEN — nested try/catch produces invalid wasm

### object_iteration.js — NEW
**Expected**: `10` **Actual**: `undefined`
**Status**: OPEN — for-in/for-of on objects not elaborated

### string_comparison.js — NEW
**Expected**: `1` **Actual**: `0`
**Status**: OPEN — string comparison operators not working in Wasm
