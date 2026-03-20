
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

## Run: 2026-03-20T18:15:01+00:00

- Implemented:
  - **Wasm/Semantics.lean — 8 correctness fixes**:
    1. `i32.clz`, `i32.ctz`, `i32.popcnt`: Implemented actual counting algorithms (were returning input unchanged). Added top-level `clzGo`/`ctzGo`/`popcntGo` with proper termination proofs.
    2. `i64.clz`, `i64.ctz`, `i64.popcnt`: Same fix for 64-bit variants.
    3. `f32.store`, `f64.store`: Now write actual float bit patterns via `floatToU32Bits`/`floatToU64Bits` (were writing 0).
    4. `i32.load8_s`, `i32.load16_s`: Added sign extension via `signExtend32` (were zero-extending like _u).
    5. `i64.load8_s`, `i64.load16_s`, `i64.load32_s`: Added sign extension via `signExtend64` (were zero-extending).
    6. `f32.convert_i32_s`, `f64.convert_i32_s`: Now use `Float.ofInt (i32ToSigned n)` for signed conversion (were using unsigned `Float.ofNat`).
    7. `f32.reinterpret_i32`, `f64.reinterpret_i64`: Now use `u32BitsToFloat`/`u64BitsToFloat` for bit-level reinterpret (were using `Float.ofNat` numeric conversion).
    8. `f32.load`, `f64.load`: Now use bit-level reinterpretation for loaded values.
  - **Runtime/Values.lean — 6 new helpers + 15 sanity checks**:
    - `decodeToStringRef?`, `decodeToObjectRef?`, `decodeToSymbolRef?`: Extract typed payloads from NaN-boxed values.
    - `isTruthy`: ECMA-262 §7.1.2 ToBoolean implementation.
    - `isString`, `isObject`, `isNullish`: Fast tag predicates.
    - 15 new `example` unit tests verifying all new helpers.

- Files changed:
  - VerifiedJS/Wasm/Semantics.lean (added ~80 lines of helpers, rewrote ~120 lines of instruction cases)
  - VerifiedJS/Runtime/Values.lean (added ~55 lines of helpers + tests)

- Build: PASS (all 12 wasmspec-owned modules build clean, 0 sorries)

- E2E blockers identified (NOT my files — owned by `proof`):
  - **logical_ops.js**: `logAnd`/`logOr` in Emit.lean mapped to f64.mul/f64.add instead of short-circuit semantics. Fix needed in Lower.lean or Emit.lean.
  - **fibonacci.js**: `__rt_call` runtime helper (in Lower.lean) has correct source code but old binary has stub body. Rebuilding compiler should fix once Core/Semantics.lean syntax error is resolved.
  - **string_concat.js**: `__rt_binaryAdd` always does numeric add, never checks string operands. Fix needed in Lower.lean.
  - **Core/Semantics.lean:297** has syntax error (jsspec broke build) — blocks all E2E compilation.

- Gaps remaining:
  - Runtime/Regex.lean: 0% (empty stub)
  - Runtime/Generators.lean: 0% (empty stub)
  - Wasm/Semantics.lean bulk memory ops (memoryInit/Copy/Fill) are no-ops (pop+discard)
  - No formal round-trip proof for NaN-boxing encode/decode

- Next:
  - Await jsspec fix for Core/Semantics.lean:297 syntax error
  - Consider adding @[simp] equation lemmas for clz/ctz/popcnt helpers to aid proof automation
  - Port more WasmCert-Coq semantics if proof agent needs them

### Continued: WasmCert-Coq gap fixes + round-trip theorems

- Implemented:
  - **call_indirect type check** (critical spec gap):
    - Added `types : Array FuncType` field to `Store` structure
    - Added `memLimits : Array Limits` field to `Store` structure
    - `call_indirect` now resolves expected type index from `store.types` and compares against the function's actual type. Traps on mismatch per §4.4.8.7.
    - REF: WasmCert-Coq `r_call_indirect_success/failure_mismatch`
  - **memory.grow failure case**:
    - Checks new page count against declared max limit (from `store.memLimits`)
    - On failure (exceeds max or 65536 absolute limit), returns -1 (0xFFFFFFFF) with store unchanged
    - REF: WasmCert-Coq `r_memory_grow_failure`
  - **Runtime/Values.lean — @[simp] theorems for proof automation**:
    - `decode_encodeNull`, `decode_encodeUndefined`, `decode_encodeBool`
    - `decodeToBool_encodeBool`, `isTruthy_encodeBool`
    - `isTruthy_encodeNull`, `isTruthy_encodeUndefined`
    - `isBoxed_encode*`, `getTag_encode*`
  - **Wasm/Semantics.lean — native_decide sanity checks**:
    - 7 examples for i32Clz/Ctz/Popcnt verifying concrete values

- Files changed:
  - VerifiedJS/Wasm/Semantics.lean (Store gains `types`/`memLimits` fields, call_indirect rewritten, memory.grow rewritten)
  - VerifiedJS/Runtime/Values.lean (+12 @[simp] theorems)

- Build: PASS (all 15 wasmspec-dependent modules build clean)

