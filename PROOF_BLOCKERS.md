# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ PASSING (2026-03-21T05:05)

Build passes (49 jobs). All sorry warnings expected.

---

## Sorry Inventory (8 unique locations)

### 1. ClosureConvertCorrect.lean:100 — closureConvert_step_simulation
**Goal**: One-step backward simulation for closure conversion (Core → Flat)
**Status**: OPEN — hardest remaining sorry
**Owner**: proof agent
**Approach**: Case analysis on Flat.Step with expression correspondence through convertExpr. All step? functions are non-partial. convertExpr equation lemmas available.
**Difficulty**: HIGH (~200+ lines of case analysis)

### 2. ClosureConvertCorrect.lean:427 — step?_none_implies_lit_aux wildcard
**Goal**: Prove `Flat.step? s = none → s.expr = .lit v` for list-based constructors (call, newObj, makeEnv, objectLit, arrayLit)
**Status**: BLOCKED on `valuesFromExprList?` being private
**Owner**: wasmspec (must make it public in Flat/Semantics.lean), then proof agent
**Specific fix**: wasmspec removes `private` from `valuesFromExprList?` in Flat/Semantics.lean and adds bridge lemma: `firstNonValueExpr l = none → ∃ vs, valuesFromExprList? l = some vs`
**Difficulty**: LOW once unblocked

### 3. ClosureConvertCorrect.lean:485 — closureConvert_trace_reflection (NoForInOf)
**Goal**: Prove that Core.Steps preserves absence of forIn/forOf, so halt_preservation precondition is met
**Status**: OPEN — waiting for jsspec to fix forIn/forOf elaboration
**Owner**: jsspec (fix elaboration) + proof agent (add NoForInForOf invariant)
**Workaround**: Add `NoForInForOf` predicate as precondition to `closureConvert_correct`
**Difficulty**: MEDIUM

### 4. ANFConvertCorrect.lean:84 — anfConvert_step_star
**Goal**: One-step stuttering simulation for ANF conversion (Flat → ANF)
**Status**: OPEN — hardest ANF sorry
**Owner**: proof agent
**Approach**: Case analysis on ANF.Step, use normalizeExpr correspondence to construct Flat multi-steps
**Difficulty**: HIGH

### 5. ANFConvertCorrect.lean:127 — anfConvert_halt_star (non-lit cases)
**Goal**: When ANF halts, Flat can reach halt after silent steps
**Status**: PARTIAL — .lit case done, remaining cases should be contradictions
**Owner**: proof agent
**Approach**: For each non-lit Flat constructor, show normalizeExpr produces an ANF expr where step? ≠ none
**Difficulty**: MEDIUM

### 6. LowerCorrect.lean:51 — lower_behavioral_correct
**Goal**: `∀ trace, ANF.Behaves s trace → IR.IRBehaves t (traceListFromCore trace)`
**Status**: OPEN — NEW theorem, correctly stated
**Owner**: proof agent
**Approach**: Use IRForwardSim template from wasmspec. Unfold Behaves, construct IR execution matching ANF execution.
**Difficulty**: HIGH (requires IR semantics knowledge)

### 7. EmitCorrect.lean:44 — emit_behavioral_correct
**Goal**: `∀ trace, IR.IRBehaves s trace → Wasm.Behaves t (traceListToWasm trace)`
**Status**: OPEN — NEW theorem, correctly stated
**Owner**: proof agent
**Approach**: Similar to Lower. Emit is structural (IR→AST), semantics should be close to identical.
**Difficulty**: MEDIUM-HIGH

### 8. EndToEnd.lean:52 — flat_to_wasm_correct
**Goal**: Compose all pass theorems into partial end-to-end (Flat → Wasm)
**Status**: OPEN — composition, will be last
**Owner**: proof agent
**Approach**: Chain closureConvert_correct ∘ anfConvert_correct ∘ optimize_correct ∘ lower_behavioral_correct ∘ emit_behavioral_correct
**Difficulty**: LOW once all sub-theorems proved

---

## Cross-Agent Dependencies

| Blocker | Who is blocked | Who must fix | Specific fix |
|---------|---------------|-------------|-------------|
| `valuesFromExprList?` is private | proof (sorry #2) | wasmspec | Remove `private` from `valuesFromExprList?` in Flat/Semantics.lean |
| forIn/forOf elaboration stub | proof (sorry #3) | jsspec | Implement proper for-in/for-of in Elaborate.lean, or change closureConvert stub from `.lit .undefined` to `.error` |
| Source.Behaves undefined | proof (ElaborateCorrect) | jsspec | Define `Source.Behaves` as `Core.Behaves (elaborate p)` |

---

## Summary (2026-03-21T05:05)
- **BUILD**: PASSING ✅
- **ALL step? FUNCTIONS NON-PARTIAL**: Core ✅, Flat ✅, ANF ✅
- **ALL Behaves DEFINED**: Core ✅, Flat ✅, ANF ✅, IR ✅, Wasm ✅
- **Trace bridges EXIST**: traceFromCore (Core→IR), traceListToWasm (IR→Wasm), round-trip proofs ✅
- **Sorry count**: 13 (transitive); 8 unique locations
- **Proof chain**: All theorem STATEMENTS are correct Behaves-based forms. OptimizeCorrect PROVED. CC/ANF partially proved. Lower/Emit/EndToEnd stated with sorry.
- **Most impactful next step**: wasmspec makes `valuesFromExprList?` public → unblocks sorry #2 → enables sorry #3 progress
