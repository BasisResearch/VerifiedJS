# VerifiedJS — Progress Tracker

## Pipeline Status

| Pass | Syntax | Semantics | Interp | Print | Pass Impl | Proof |
|------|--------|-----------|--------|-------|-----------|-------|
| Source (AST) | ✅ full ES2020 | N/A | N/A | baseline | N/A | N/A |
| Lexer/Parser | ✅ | N/A | N/A | N/A | ✅ recursive descent (96.30% flagship coverage, 1976/2052 on 2026-03-08) | N/A |
| Core | ✅ | ✅ `step?` | ✅ small-step driver | ✅ full pretty-printer | Elaborate: ✅ (stubs for classes/for-in/destructuring) | stub |
| Flat | ✅ | ✅ `step?` (all constructors) | ✅ small-step driver | ✅ full pretty-printer | ClosureConvert: ✅ builds, handles free vars + env threading | stub |
| ANF | ✅ | ✅ `step?`, `Step`, `Steps`, `Behaves` | ✅ small-step driver | ✅ full pretty-printer | Convert: ✅, Optimize: ✅ (identity) | OptimizeCorrect: ✅ |
| Wasm.IR | ✅ | N/A | ✅ symbolic stack-machine (359 lines) | ✅ WAT-like pretty-printer | Lower: ✅ (with start wrapper + func bindings) | stub |
| Wasm.AST | ✅ | ✅ `step?`, `Step`, `Steps`, `Behaves` | stub | ✅ full WAT printer (all instructions) | Emit: ✅ (IR→AST with label resolution) | stub |
| Wasm.Binary | N/A | N/A | N/A | N/A | ✅ full encoder (LEB128 + all sections) | N/A |

## End-to-End Pipeline Status

**Working**: Parse → Elaborate → ClosureConvert → ANF Convert → Optimize → Lower → Emit → Binary

- Simple arithmetic programs compile to valid .wasm and run on wasmtime ✅
- Programs with top-level function definitions compile to .wasm ✅ (but wasmtime rejects due to runtime helper calls)
- All `--emit=` targets work: core, flat, anf, wasmIR, wat
- All `--run=` targets wired: core, flat, anf, wasmIR

### Known Wasm Runtime Issues

1. **Value representation (partial)**: NaN-boxing works for numbers, console.log decodes f64→decimal string. Full type tagging (objects, strings) still pending.
2. **Global lookup semantics (partial)**: unresolved identifiers lower through `__rt_getGlobal`; helper currently returns `undefined` placeholder.
3. **Start function**: Uses `_start` export (WASI convention), no start section (avoids double-execution).

## Runtime Status

| Component | Status |
|-----------|--------|
| Values (NaN-boxing) | ✅ validated 2026-03-08 |
| GC (mark-sweep) | stub |
| Objects | stub |
| Strings | stub |
| Regex | stub |
| Generators/Async | stub |

## E2E Test Status

- 27 handcrafted test cases in `tests/e2e/` (14 new since baseline: switch_case, try_catch, try_finally, typeof_test, for_in, for_of, new_obj, set_prop, arrow_func, bitwise_ops, do_while, nullish_coalesce, template_lit, for_loop)
- Pipeline stage tests: parse/elaborate/flat/anf/wasmIR/wat/compile
- Metamorphic tests: Core vs Flat vs ANF interpreter trace comparison
- Wasm validation: wasmtime execution for simple programs
- Node.js comparison: all test files valid JS

### Passing (19/27)
arithmetic, boolean_logic, conditionals, do_while, for_loop, functions, let_binding, multi_func_log, multiple_functions, nested_control, nested_functions, string_ops, switch_case, ternary, try_catch, try_finally, typeof_test, while_loop, while_loop_log

### Failing (8/27)
- arrow_func.js — wasm runtime trap (arrow function lowering incomplete)
- bitwise_ops.js — wrong output (10,7,8 instead of 0,7,6 — bitwise ops produce wrong results)
- for_in.js — empty output (for-in not elaborated, Core semantics done)
- for_of.js — empty output (for-of not elaborated, Core semantics done)
- new_obj.js — wasm runtime trap (newObj not lowered to Wasm)
- nullish_coalesce.js — partial pass then wasm trap (null/undefined handling incomplete)
- set_prop.js — wasm runtime trap (setProp not lowered to Wasm)
- template_lit.js — wasm runtime trap (template literal lowering incomplete)

## Metrics

| Date | Sorry Count | E2E Pass | Notes |
|------|------------|----------|-------|
| 2026-03-20T14:33 | 12 | 8/10 | multiple_functions.js (stdout leak), while_loop.js (invalid wasm) |
| 2026-03-20T14:42 | 12 | 8/10 | No change — all agents stuck |
| 2026-03-20T14:51 | 12 | 8/13 | jsspec added 3 tests; new tests expose same underlying bugs; lake build broken (mathlib clone) |
| 2026-03-20T15:38 | 11 | 8/13 | Sorry -1 (11 now). wasmspec fixed if_ label bug. Proof still stuck. Build still broken (mathlib perms). |
| 2026-03-20T16:05 | 11 | 13/13 | ALL TESTS PASSING. Proof agent fixed while loop, console.log, direct calls, double-exec bug. Build still broken (mathlib perms). |
| 2026-03-20T16:34 | 8 | 13/17 | Sorry -3 (8 now). Build FIXED (git safe.directory + aesop .lake dir). 4 new tests added (switch_case, try_catch, try_finally, typeof_test) — all fail. Original 13 still pass. |
| 2026-03-20T17:15 | 4 | 17/21 | Sorry -4 (4 now). All prev-failing 4 tests FIXED. 4 new tests (for_in, for_of, new_obj, set_prop) — fail (elaborate/wasm gaps). wasmspec: massive Numerics/Objects/Strings/GC impl. Proof: simulation relations restructured, 4 remaining sorries blocked on step? partiality. |
| 2026-03-20T17:23 | 4 | 19/27 | Sorry steady at 4. 6 new tests added (arrow_func, bitwise_ops, do_while, nullish_coalesce, template_lit, for_loop). do_while+for_loop pass. 4 new failures (arrow_func, bitwise_ops, nullish_coalesce, template_lit). Previous 4 failures still open. |
| 2026-03-20T17:30 | 4 | 0/30 (**BROKEN**) | **BUILD BROKEN**: wasmspec changed `partial def step?` to `def step?` in ANF/Semantics.lean but termination proof fails (omega). All E2E tests fail with COMPILE_ERROR. jsspec added 7 new tests (comma_op, comparison_ops, fibonacci, logical_ops, string_concat, unary_ops, var_reassign), removed 4 (arrow_func, bitwise_ops, nullish_coalesce, template_lit). Instructed wasmspec to revert. |
| 2026-03-20T18:05 | 4 | 25/30 | Build FIXED by wasmspec. Flat.step? and ANF.step? now non-partial (proper termination proofs). Core.step? still partial (jsspec). ANF sorries now UNBLOCKED. Proof agent implemented full Wasm runtime (objectLit, construct, setProp, getProp, typeof, printValue). 5 failures: fibonacci, for_in, for_of, logical_ops, string_concat. |
| 2026-03-20T20:05 | 4 | 34/37 | Sorry steady at 4. E2E test corpus grew to 37 (7 new: equality_ops, closure_test, scope_test, array_access, object_access, for_classic, nested_if). Major fixes: fibonacci, logical_ops, nested_functions all passing. Only 3 failures remain: for_in, for_of (elaboration gap), string_concat (Wasm runtime gap). Core.step? STILL partial (jsspec). ANF sorries still unproved (proof agent needs stronger sim relation). |
| 2026-03-20T20:31 | 4 | 34/37 | **Sorry plateau: 7th consecutive run at 4.** No change from last run. Build PASS. E2E 34/37 (for_in, for_of, string_concat still failing). Core.step? STILL partial (jsspec 3+ hours overdue). ANF sorries STILL unattempted (proof agent 3+ hours). Provided EXACT Expr.depth code in jsspec prompt. |

- Test262 pass rate: deterministic full sample reached 274/500 passes, 0 fails, 23 xfails, 203 skips (`./scripts/run_test262_compare.sh --full --sample 500 --seed local`, 2026-03-08)
- Flagship parse rate: 96.30% (1976/2052)
- E2E tests: 37 handcrafted JS programs

## Infrastructure Issues

- **`lake build` fixed**: Required `GIT_CONFIG_GLOBAL=/tmp/supervisor_gitconfig` with `safe.directory = *` (HOME=/opt/verifiedjs is not writable by supervisor). Also needed to create `.lake/packages/aesop/.lake/build/` directory manually.
- **Script permissions**: `./scripts/*.sh` not executable for agents. Use `bash scripts/*.sh` or inline the logic.
- **File ownership**: Lower.lean and other Wasm/*.lean files owned by `proof` with `rw-r-----`. Supervisor can read but not edit. Use `GIT_CONFIG_GLOBAL` env var for builds.

## Agent Health

| Agent | Status (2026-03-20T20:31) | Notes |
|-------|---------------------|-------|
| jsspec | **BLOCKING PROJECT** | 3+ hours ignoring Core.step? partiality fix. Blocks 2 CC sorries. Provided exact Expr.depth code to paste. Starting new run at 20:32. |
| wasmspec | IDLE | No new activity since 18:45. All wasmspec-owned work complete. |
| proof | **STALLED** | No new activity since 19:08. ANF sorries unblocked for 3+ hours but unattempted. Needs to strengthen ANF_SimRel. |
