
## Run: 2026-03-20T16:32:23+00:00

- Implemented:
  - **Wasm.Numerics**: Complete rewrite from 10 operations to 100+ operations covering ALL Wasm 1.0 numeric instructions:
    - i32/i64: add, sub, mul, div_s/u, rem_s/u, and, or, xor, shl, shr_s/u, rotl, rotr, clz, ctz, popcnt, eqz
    - i32/i64 comparisons: eq, ne, lt_s/u, gt_s/u, le_s/u, ge_s/u
    - f32/f64: add, sub, mul, div, min (NaN-propagating), max (NaN-propagating), copysign
    - f32/f64 unary: abs, neg, ceil, floor, trunc, nearest, sqrt
    - f32/f64 comparisons: eq, ne, lt, gt, le, ge
    - Conversions: i32.wrap_i64, i64.extend_i32_s/u, trunc_f*_s/u, convert_i*_s/u, demote, promote, reinterpret
    - Sign extension ops: i32.extend8_s, i32.extend16_s, i64.extend8_s, i64.extend16_s, i64.extend32_s
    - Helper: truncFloatToInt? for safe float-to-int conversion
  - **Runtime/Objects.lean**: From 0% to functional — property descriptors, object records, object heap with alloc/get/set/delete/has/hasOwn/ownKeys, prototype chain traversal with fuel-bounded termination, linear memory layout spec
  - **Runtime/Strings.lean**: From 0% to functional — UTF-16 code units, JSString type, string interning table with intern/get/size, string operations (length, charAt, charCodeAt, concat, slice, equal, lessThan, indexOf), UTF-16 encoding (charToUTF16, stringToJSString, jsStringToString), linear memory layout spec
  - **Runtime/GC.lean**: From stub to allocator specification — GCState, Allocation, AllocatorState, bumpAlloc with 4-byte alignment, GCState.init, freeSpace/totalAllocated, axiomatized gc_preserves_reachable (TCB boundary)

- Files changed:
  - VerifiedJS/Wasm/Numerics.lean (26 lines -> 420+ lines)
  - VerifiedJS/Runtime/Objects.lean (13 lines -> 165+ lines)
  - VerifiedJS/Runtime/Strings.lean (13 lines -> 180+ lines)
  - VerifiedJS/Runtime/GC.lean (18 lines -> 100+ lines)

- Build: PASS (all 4 files + Wasm/Semantics.lean verified clean)

- Gaps remaining:
  - Semantics.lean still inlines some numeric ops (could be refactored to use Numerics.*)
  - Runtime/Regex.lean: 0% (regex AST, NFA, DFA — lower priority)
  - Runtime/Generators.lean: 0% (generator state machines — lower priority)
  - Wasm/Interp.lean: 0% (execution loop — stub with sorry)
  - Wasm/Lower.lean: 3 proof sorries (lowerStartIsNone, lowerExportsCorrect, lowerMemoriesCorrect)
  - Proofs/ANFConvertCorrect.lean: 3 sorry lemmas
  - Proofs/ClosureConvertCorrect.lean: 3 sorry lemmas

- Next:
  - Port more from WasmCert-Coq if needed
  - Implement Regex.lean if compiler emits regex operations
  - Fill Generators.lean if async/generator support is prioritized
  - Consider refactoring Semantics.lean inline ops to use Numerics.* for cleaner proof structure
2026-03-20T17:13:38+00:00 DONE

## Run: 2026-03-20T17:25:10+00:00

- Implemented:
  - **ANF.step? made non-partial**: Removed `partial` from `ANF.Semantics.step?`, added `Expr.depth` measure to ANF.Syntax.lean, proved termination via `termination_by s.expr.depth` with `decreasing_by` tactic handling Option Expr case-split for tryCatch. ANF proofs can now unfold/case-split on `step?`.
  - **Flat.step? made non-partial**: Major restructuring — removed 5 `let rec` inner helpers (`stepCallArgs`, `stepNewObjArgs`, `stepValues`, `stepProps`, `stepElems`) that called `step?` on list elements. Replaced with standalone `firstNonValueExpr`/`firstNonValueProp` helpers + `have` termination proofs inside `step?`. Added mutual `Expr.depth`/`Expr.listDepth`/`Expr.propListDepth` to Flat.Syntax.lean, plus `firstNonValueExpr_depth`/`firstNonValueProp_depth` theorems proving list element depth < list depth.
  - **GC.lean**: Fixed unused variable linter warnings.
  - **Impact**: Unblocked ANFConvertCorrect.lean proofs (2 sorries) — both Flat.step? and ANF.step? are now non-partial, allowing unfold/case-split reasoning. Partially unblocked ClosureConvertCorrect.lean (Flat.step? non-partial, but Core.step? still needs jsspec to fix).

- Files changed:
  - VerifiedJS/ANF/Syntax.lean (added Expr.depth: 16 lines)
  - VerifiedJS/ANF/Semantics.lean (partial → def + termination_by)
  - VerifiedJS/Flat/Syntax.lean (added depth functions, firstNonValue helpers, 4 theorems: ~110 lines)
  - VerifiedJS/Flat/Semantics.lean (major rewrite: partial → def, removed let rec helpers, added have proofs)
  - VerifiedJS/Runtime/GC.lean (unused variable fix)

- Build: PASS (49 jobs, 0 errors, 4 sorry warnings in proof files only)
- E2E: 30/30 valid wasm files

- Gaps remaining:
  - Core.step? still partial (jsspec ownership, not wasmspec)
  - ClosureConvertCorrect.lean: 2 sorries (blocked on Core.step? being partial)
  - ANFConvertCorrect.lean: 2 sorries (NOW UNBLOCKED — proof agent can attempt these)
  - Runtime/Regex.lean: 0% (not used by compiler)
  - Runtime/Generators.lean: 0% (not used by compiler)

- Next:
  - Proof agent should attempt ANFConvertCorrect.lean sorries (both step? functions now non-partial)
  - jsspec needs to make Core.step? non-partial to unblock ClosureConvertCorrect.lean
  - Consider adding @[simp] equation lemmas for step? to aid proof automation

2026-03-20T17:51:23+00:00 DONE
