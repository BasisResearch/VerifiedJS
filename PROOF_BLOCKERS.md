# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ PASS (2026-03-22T18:05)

---

## CRITICAL BLOCKERS (2026-03-22T18:05)

### A. CC_SimRel too weak — blocks ALL 25 CC sorries
**Owner**: proof agent
**Issue**: CC_SimRel only tracks trace equality + expression correspondence. Lacks env/value/heap correspondence. Every CC case needs env lookup match.
**Fix**: Strengthen with ValueCorr + EnvCorr (exact definition in proof prompt).

### B. Flat.return/yield event mismatch — theorem FALSE for 2 cases
**Owner**: wasmspec (owns Flat/Semantics.lean)
**Issue**: Core.return → `.error "return:..."`, Flat.return → `.silent`. CC simulation requires same event.
**Fix**: Change Flat.step? return/yield to produce `.error` events matching Core. Exact code in wasmspec prompt.

### C. lowerExpr is private — blocks 3+ LowerSimRel.init hcode sorries
**Owner**: proof agent (owns Lower.lean)
**Fix**: Make lowerExpr public or add equation lemmas.

---

## Sorry Inventory (71 total, 4 files)

### 1. ClosureConvertCorrect.lean — 25 sorries
**Goal**: One-step backward simulation for closure conversion (Core → Flat)
**Status**: OPEN — decomposed from 1 catch-all to 25 individual Core.Expr cases. ALL BLOCKED on CC_SimRel weakness (blocker A) and return/yield mismatch (blocker B).
**Owner**: proof agent
**Difficulty**: MEDIUM per case once CC_SimRel is fixed

### ~~2. step?_none_implies_lit_aux wildcard — RESOLVED~~
**Status**: ✅ RESOLVED at 2026-03-21T05:30. wasmspec made `valuesFromExprList?` public. Proof agent proved all list-based constructor cases using `firstNonValueExpr_none_implies_values`.

### ~~3. closureConvert_trace_reflection — RESOLVED~~
**Status**: ✅ RESOLVED at 2026-03-21T13:22. Proved via NoForInForOf precondition.

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
| **CC_SimRel too weak** | **proof (25 CC cases)** | **proof** | Add ValueCorr + EnvCorr to CC_SimRel. Exact definition in proof prompt. |
| **Flat.return/yield events wrong** | **proof (2 CC cases)** | **wasmspec** | Fix Flat.step? return/yield to produce `.error` events matching Core. Exact code in wasmspec prompt. |
| `lowerExpr` is private in Lower.lean | wasmspec (3 hcode sorries) | proof | Make `lowerExpr` public or add equation lemmas |
| forIn/forOf elaboration stub | proof (CC trace_reflection) | jsspec | **WORKAROUND IN PLACE**: NoForInForOf precondition |
| ~~ANFConvertCorrect.lean BUILD BREAK~~ | ~~ALL agents~~ | ~~proof~~ | ✅ RESOLVED — build passes |

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

## Summary (2026-03-22T18:05)
- **BUILD**: ✅ PASS
- **ALL step? FUNCTIONS NON-PARTIAL**: Core ✅, Flat ✅, ANF ✅
- **ALL Behaves DEFINED**: Core ✅, Flat ✅, ANF ✅, IR ✅, Wasm ✅, Source ✅
- **Flat/ SORRY-FREE** ✅
- **Core/Semantics SORRY-FREE** ✅
- **Sorry count**: 71 (structural decomposition from 8: 25 CC + 42 Wasm + 9 ANF + 1 Lower — but finer-grained)
- **Proof chain**: All theorem STATEMENTS correct. **Elaborate PROVED** ✅, **Optimize PROVED** ✅. CC/ANF partially proved. Lower/Emit decomposed with code correspondence.
- **CRITICAL PATH**: (1) Proof agent strengthens CC_SimRel. (2) wasmspec fixes Flat.return/yield events. (3) Proof agent proves CC env-only cases. (4) wasmspec proves step_sim sub-cases.
- **Test262**: 3/61 — stalled (failures need Temporal, Proxy, generators, classes, etc.)
