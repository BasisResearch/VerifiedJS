# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ PASSING (2026-03-21T13:20)

Build passes (49 jobs). All sorry warnings expected.

---

## Sorry Inventory (7 unique locations)

### 1. ClosureConvertCorrect.lean:138 — closureConvert_step_simulation
**Goal**: One-step backward simulation for closure conversion (Core → Flat)
**Status**: OPEN — hardest remaining sorry
**Owner**: proof agent
**Approach**: Case analysis on Flat.Step with expression correspondence through convertExpr. All step? functions are non-partial. convertExpr equation lemmas available.
**Difficulty**: HIGH (~200+ lines of case analysis)

### ~~2. step?_none_implies_lit_aux wildcard — RESOLVED~~
**Status**: ✅ RESOLVED at 2026-03-21T05:30. wasmspec made `valuesFromExprList?` public. Proof agent proved all list-based constructor cases using `firstNonValueExpr_none_implies_values`.

### 3. ClosureConvertCorrect.lean:672 — closureConvert_trace_reflection
**Goal**: Compose step_simulation + halt_preservation into trace_reflection
**Status**: BLOCKED on sorry #1 (step_simulation). Once step_simulation is proved, this should follow automatically.
**Owner**: proof agent
**Difficulty**: LOW once step_simulation is proved

### 4. ANFConvertCorrect.lean:84 — anfConvert_step_star
**Goal**: One-step stuttering simulation for ANF conversion (Flat → ANF)
**Status**: OPEN — hardest ANF sorry
**Owner**: proof agent
**Approach**: Case analysis on ANF.Step, use normalizeExpr correspondence to construct Flat multi-steps. normalizeExpr is now public (non-private).
**Difficulty**: HIGH

### 5. ANFConvertCorrect.lean:127 — anfConvert_halt_star (non-lit cases)
**Goal**: When ANF halts, Flat can reach halt after silent steps
**Status**: PARTIAL — .lit case done, remaining cases should be contradictions
**Owner**: proof agent
**Approach**: For each non-lit Flat constructor, show normalizeExpr produces an ANF expr where step? ≠ none. This contradicts `hhalt : ANF.step? sa = none`.
**Tactic hint**: Try `cases hlit : sf.expr with | var => ... | seq => ...` — for each constructor, unfold `normalizeExpr`, show the result always has `step? ≠ none` (it's a let-binding or compound expr, not a stuck literal).
**Difficulty**: MEDIUM — best next target for sorry reduction

### 6. LowerCorrect.lean:51 — lower_behavioral_correct
**Goal**: `∀ trace, ANF.Behaves s trace → IR.IRBehaves t (traceListFromCore trace)`
**Status**: OPEN — correctly stated
**Owner**: proof agent
**Approach**: Unfold ANF.Behaves to get ANF.Steps + halt. Construct matching IR.IRSteps using the 19+ exact-value equation lemmas wasmspec added (irStep?_eq_*). Use IRSteps_cons/IRSteps_two/IRSteps_three composition helpers.
**Difficulty**: HIGH (requires understanding both ANF and IR semantics)

### 7. EmitCorrect.lean:44 — emit_behavioral_correct
**Goal**: `∀ trace, IR.IRBehaves s trace → Wasm.Behaves t (traceListToWasm trace)`
**Status**: OPEN — correctly stated
**Owner**: proof agent
**Approach**: Emit is structural (IR→AST). Show IR.IRStep maps to Wasm.Step by instruction correspondence.
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
| ~~`valuesFromExprList?` is private~~ | ~~proof~~ | ~~wasmspec~~ | ✅ RESOLVED 2026-03-21T05:15 |
| forIn/forOf elaboration stub | proof (CC trace_reflection) | jsspec | Implement proper for-in/for-of in Elaborate.lean, or change closureConvert stub from `.lit .undefined` to `.error`. **WORKAROUND IN PLACE**: NoForInForOf precondition added to closureConvert_correct. |
| Source.Behaves undefined | proof (ElaborateCorrect) | jsspec | Define `Source.Behaves` as `Core.Behaves (elaborate p)` |

---

## Priority Ranking for Sorry Reduction

**Best bang-for-buck** (attack in this order):
1. **anfConvert_halt_star non-lit** (#5) — MEDIUM difficulty, most cases are contradictions. Prove that for each non-lit Flat constructor, normalizeExpr produces an ANF expression that always steps.
2. **lower_behavioral_correct** (#6) — HIGH but wasmspec provided 19+ exact-value lemmas. Start by unfolding Behaves and constructing IR execution for a simple program (e.g., lit → lit lowering).
3. **closureConvert_step_simulation** (#1) — HARDEST, but the most impactful. Resolving this auto-resolves #3 (trace_reflection).
4. **anfConvert_step_star** (#4) — HARDEST for ANF. Similar structure to #1.
5. **emit_behavioral_correct** (#7) — structural, similar to #6.
6. **flat_to_wasm_correct** (#8) — composition, last.

---

## Summary (2026-03-21T13:20)
- **BUILD**: PASSING ✅
- **ALL step? FUNCTIONS NON-PARTIAL**: Core ✅, Flat ✅, ANF ✅
- **ALL Behaves DEFINED**: Core ✅, Flat ✅, ANF ✅, IR ✅, Wasm ✅
- **Trace bridges EXIST**: traceFromCore (Core→IR), traceListToWasm (IR→Wasm), round-trip proofs ✅
- **Sorry count**: 7 direct sorry locations
- **Proof chain**: All theorem STATEMENTS correct. OptimizeCorrect PROVED. CC/ANF partially proved. Lower/Emit/EndToEnd stated with sorry.
- **Key blocker resolved**: valuesFromExprList? now public ✅
- **Most impactful next step**: proof agent attacks anfConvert_halt_star non-lit cases (best ROI)
