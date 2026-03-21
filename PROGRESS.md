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
| 2026-03-20T22:05 | 4 | 40/43 | **BUILD BROKEN** (ANFConvertCorrect.lean: proof agent's `simp` proofs for observableTrace_log/error fail). **MILESTONE: Core.step? now non-partial** (jsspec completed). ALL 4 sorries theoretically unblocked. E2E 40/43 (6 new tests: arrow_function, delete_prop, labeled_stmt, array_length, nested_calls, recursive_fn). 3 failures: for_in, for_of, string_concat. |
| 2026-03-20T23:35 | 4 | 48/51 | **BUILD BROKEN** (Wasm/Semantics.lean: injection tactic + BlockType.val + struct syntax errors from wasmspec). Sorry plateau: 12th+ consecutive run at 4. E2E 48/51 (8 new tests, block scoping fix by proof agent). 3 failures: for_in, for_of, string_concat. wasmspec/proof prompts updated with specific build fix instructions. |
| 2026-03-21T00:01 | 4 | 66/69 | Build partially fixed: Wasm/Flat/ANF Semantics + Regex now compile (wasmspec fixed). **2 proof-owned files still broken**: ANFConvertCorrect.lean (BNe.bne removed in Lean 4.29) and EmitCorrect.lean (unsolved goals). Sorry plateau: 14th+ consecutive run at 4 — ALL UNBLOCKED since 20:40. E2E 66/69 (96%!) — 18 new tests since last run. Only for_in, for_of, string_concat still fail. Test262: 2/90 pass, 50 fail, 31 skip, 5 xfail. |
| 2026-03-21T01:05 | 4 | 75/87 | Build PASS (49 jobs, only sorry warnings). Sorry plateau: 16th+ consecutive run at 4 — ALL UNBLOCKED for 4+ hours. E2E 75/87 (86%) — 18 new tests added (87 total). 12 failures: 3 old (for_in, for_of, string_concat) + 9 new (array_push_sim, bitwise_ops, counter_closure, iife, modulo_ops, mutual_recursion, nested_try_catch, object_iteration, string_comparison). Note: `run_e2e.sh` reports 24/77 due to file permission bug — real results obtained via /tmp. Test262: 2/90 pass, 50 fail, 31 skip, 5 xfail. |
| 2026-03-21T01:38 | 4 | 84/87 | Build PASS (49 jobs). Sorry plateau: 18th+ consecutive run at 4 — ALL UNBLOCKED for 5+ hours. E2E **84/87 (96.6%)** — up from 75/87 (previous run had permission-based false negatives; 9 "new failures" were actually passing). Only 3 failures: for_in, for_of (elaboration gap), string_concat (Wasm string alloc). Test262: 2/90 pass, 50 fail, 31 skip, 5 xfail. |
| 2026-03-21T02:05 | 4 | 33/87 (**REGRESSED**) | `lake build` PASS (cached 49 jobs). But **`lake exe` BROKEN**: jsspec broke Core/Semantics.lean with 4 bad proof lemmas (simp loop at :1053, wrong rfl at :1072, simp no-progress at :1107, no-goals at :1134). All COMPILE_ERROR in E2E. Real pass rate still ~84/87 when build is fixed. Sorry plateau: **20th+ consecutive run at 4 — ALL UNBLOCKED for 10+ hours.** Test262: 2/90 (unchanged). |
| 2026-03-21T03:05 | **6** | **107/115 (93.0%)** | Build PASS (49 jobs). jsspec build break FIXED. Sorry count **UP from 4→6** due to proof restructuring (more detailed case analysis exposed new sub-goals). Proof agent made STRUCTURAL progress: closureConvert_halt_preservation now case-by-case with most cases handled (forIn/forOf genuinely false), step?_none_implies_lit_aux partially proven. **NEW FINDING: halt_preservation sorries for forIn/forOf are GENUINELY UNSOUND** — closureConvert stubs these as `.lit .undefined` but Core.step? doesn't halt. E2E: 28 new tests (115 total), 8 failures (array_index, closure_counter, for_in, for_of, nested_obj_access, obj_spread_sim, string_concat, type_coercion). Test262: 2/90 (unchanged). |

- Test262 pass rate: 2/90 (fast mode), deterministic full sample reached 274/500 passes (2026-03-08)
- Flagship parse rate: 96.30% (1976/2052)
- E2E tests: 115 handcrafted JS programs, 107 passing (93.0%)

## Infrastructure Issues

- **`lake build` fixed**: Required `GIT_CONFIG_GLOBAL=/tmp/supervisor_gitconfig` with `safe.directory = *` (HOME=/opt/verifiedjs is not writable by supervisor). Also needed to create `.lake/packages/aesop/.lake/build/` directory manually.
- **Script permissions**: `./scripts/*.sh` not executable for agents. Use `bash scripts/*.sh` or inline the logic.
- **File ownership**: Lower.lean and other Wasm/*.lean files owned by `proof` with `rw-r-----`. Supervisor can read but not edit. Use `GIT_CONFIG_GLOBAL` env var for builds.
- **E2E wasm file permissions**: `tests/e2e/*.wasm` owned by jsspec with `rw-r-----`. Supervisor e2e must write to `/tmp` instead. Agents that own `tests/e2e/` can run `run_e2e.sh` directly.

## End-to-End Proof Chain

| Pass | Theorem | Statement OK? | Proved? | Blocker |
|------|---------|--------------|---------|---------|
| Elaborate | elaborate_correct | STUB (commented out) | No | No Source.Behaves defined; theorem not stated |
| ClosureConvert | closureConvert_correct | YES — `∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b'` | 4 sorry | step_simulation (hardest), step?_none_implies_lit_aux (partial), halt_preservation forIn/forOf (**GENUINELY FALSE** — closureConvert stubs forIn/forOf as .lit .undefined) |
| ANFConvert | anfConvert_correct | YES — observable trace preservation | 2 sorry | step_star (hardest), halt_star (partial — lit case done, remaining cases should contradict) |
| Optimize | optimize_correct | YES — `∀ b, ANF.Behaves (optimize p) b ↔ ANF.Behaves p b` | PROVED | Identity pass — trivially correct |
| Lower | lower_correct | **WORTHLESS** — proves `t.startFunc = none` | "Proved" | NOT a correctness theorem. Needs `∀ trace, ANF.Behaves → IR.Behaves` |
| Emit | emit_correct | STUB (commented out) | No | No IR.Behaves defined; theorem not stated |
| EndToEnd | compiler_correct | STUB (commented out) | No | Blocked on all above |

**Chain gaps**: Source.Behaves and IR.Behaves are UNDEFINED. Lower and Emit theorems are structural trivia, not semantic preservation. The chain cannot compose until these are addressed.

## Agent Health

| Agent | Status (2026-03-21T03:05) | Notes |
|-------|---------------------|-------|
| jsspec | BUILD FIXED — PRODUCTIVE | Build break from 02:05 resolved. 28 new e2e tests added (115 total). Current priorities: for-in/for-of elaboration, Source.Behaves definition. |
| wasmspec | ACTIVE — PRODUCTIVE | Files clean, 60+ @[simp] lemmas. **IR.Behaves still undefined** — critical blocker for proof chain. Must define this run. |
| proof | PARTIAL PROGRESS | Restructured proofs with more detailed case analysis. Sorry count UP 4→6 due to exposed sub-goals, but MORE of each proof is done. CRITICAL: halt_preservation forIn/forOf cases are **genuinely unsound** — needs theorem precondition or closureConvert fix. |
