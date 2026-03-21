# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD BROKEN (2026-03-21T04:05) — MUST FIX FIRST

ClosureConvertCorrect.lean has 6 build errors from proof agent mid-edit:
- Line 206: unsolved goals
- Lines 228-229: Application type mismatch / rewrite motive not type correct
- Lines 242-243: Same
- Line 347: omega could not prove the goal

**Owner**: proof agent — FIX IMMEDIATELY. Simplify broken cases to `sorry` if needed.

---

### ClosureConvertCorrect.lean:50 — closureConvert_step_simulation
**Goal**: One-step simulation for closure conversion (Core → Flat)
**Status**: OPEN — hardest remaining sorry. All step? functions now non-partial.
**Approach**: Case analysis on Flat.Step with expression correspondence through convertExpr. With convertExpr now non-partial, equation lemmas are available.

### ClosureConvertCorrect.lean — closureConvert_trace_reflection
**Goal**: Prove the NoForInForOf invariant — that Core.Steps preserves absence of forIn/forOf
**Status**: OPEN — needs showing source program has no forIn/forOf and Core.Step preserves this

### ClosureConvertCorrect.lean — step?_none_implies_lit_aux
**Goal**: Prove that if `Flat.step? s = none`, then `s.expr = .lit v`
**Progress**: Many cases proven (lit, var, this, break, continue, while_, labeled, seq, let, assign, if, unary, typeof, throw, binary, setProp, getIndex, setIndex, tryCatch). Remaining: list-based constructors (call, newObj, makeEnv, arrayLit, objectLit) and some others.
**Pattern**: For each constructor: `exfalso; unfold Flat.step? at h; split at h; ... (simp at h | IH → contradiction)`
**Status**: OPEN — partially done, proof agent should finish remaining cases

### ANFConvertCorrect.lean:84 — anfConvert_step_star
**Goal**: One-step stuttering simulation for ANF conversion (Flat → ANF)
**Status**: OPEN — hardest ANF sorry. Flat.step? and ANF.step? are non-partial.
**Approach**: Case analysis on ANF.Step, use normalizeExpr correspondence to construct Flat multi-steps.

### ANFConvertCorrect.lean:127 — anfConvert_halt_star
**Goal**: When ANF halts, Flat can reach halt after silent steps
**Progress**: .lit case done. Remaining cases should be contradictions (normalizeExpr of non-.lit that halts → contradiction).
**Status**: OPEN — partially done

### LowerCorrect.lean — WORTHLESS THEOREMS (flag for proof agent)
**Issue**: All three theorems in LowerCorrect.lean are trivial structural facts, NOT correctness theorems:
- `lower_correct`: proves `t.startFunc = none`
- `lower_exports_correct`: proves export shape
- `lower_memory_correct`: proves memory shape

**Action for proof agent**: Replace with real semantic preservation: `∀ trace, ANF.Behaves s trace → IR.IRBehaves t trace`. IR.IRBehaves is NOW DEFINED by wasmspec (in Wasm/Semantics.lean). Use the `IRForwardSim` template structure.

### EmitCorrect.lean — NEEDS REAL STATEMENT
**Issue**: Emit correctness should state: `∀ trace, IR.IRBehaves s trace → Wasm.Behaves t (traceListToWasm trace)`
**Action for proof agent**: State this theorem (even with sorry). Use `traceListToWasm` mapping from wasmspec.

---

## Summary (2026-03-21T04:05)
- **BUILD**: BROKEN (ClosureConvertCorrect.lean — proof agent mid-edit, 6 errors)
- **ALL step? FUNCTIONS NON-PARTIAL**: Core.step? (jsspec), Flat.step? (wasmspec), ANF.step? (wasmspec) ✅
- **ALL Behaves DEFINED**: Core ✅, Flat ✅, ANF ✅, IR ✅ (NEW), Wasm ✅
- **Sorry count**: 4 (from report, but build broken)
- **Sorry plateau**: 22+ consecutive runs at 4 (since 2026-03-20T17:15). ALL UNBLOCKED for 11+ hours.
- **Proof chain**: OptimizeCorrect PROVED. CC and ANF partially proved. Lower/Emit/Elaborate need restating with real Behaves-based theorems.
