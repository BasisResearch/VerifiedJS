# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ PASS (2026-03-23T09:05)

---

## CRITICAL BLOCKERS (2026-03-23T08:05)

### ~~A. CC EnvCorr is one-directional~~ — ✅ RESOLVED (2026-03-22)
### ~~B. Flat.return/yield event mismatch~~ — ✅ RESOLVED (2026-03-22T20:00)
### ~~D. Flat.toNumber returns 0.0 instead of NaN~~ — ✅ RESOLVED
### ~~E. Flat.evalUnary .bitNot returns .undefined~~ — ✅ RESOLVED
### ~~F. Flat.throw uses literal "throw"~~ — ✅ RESOLVED
### ~~G. Core/Flat .return uses repr~~ — ✅ RESOLVED
### ~~H. Flat.initialState uses Env.empty~~ — ✅ RESOLVED
### ~~I. updateBindingList private in Flat~~ — ✅ RESOLVED

### C. lowerExpr is private — blocks 3+ LowerSimRel.init hcode sorries
**Owner**: proof agent (owns Lower.lean)
**Fix**: Make lowerExpr public or add equation lemmas.

### ~~J. Flat.evalBinary misaligned with Core.evalBinary~~ — ✅ RESOLVED (2026-03-23T04:15)
wasmspec aligned Flat.evalBinary with Core.evalBinary. `abstractEq`, `abstractLt`, all operators now match. The `.binary` sorry at CC line 206 is NOW UNBLOCKED.

---

## Sorry Inventory (77 total, 4 files)

### 1. ClosureConvertCorrect.lean — 27 sorries
**Goal**: One-step backward simulation for closure conversion (Core → Flat)
**Status**: PARTIAL — .if/.typeof/.await/.yield(some)/.let/.seq/.var/.return-none/.break/.continue/.labeled PROVED. 5+ cases BLOCKED on Flat semantic bugs (D/E/F/G/H/I). .binary ready to prove.
**Owner**: proof agent
**Difficulty**: MEDIUM per case once Flat bugs fixed

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
| **Flat.toNumber wrong (D)** | **proof (.unary/.binary CC)** | **wasmspec** | Match Core.toNumber — exact code in prompt |
| **Flat.bitNot wrong (E)** | **proof (.unary CC)** | **wasmspec** | Match Core.evalUnary .bitNot — exact code in prompt |
| **Flat.throw event (F)** | **proof (.throw CC)** | **wasmspec** | Define valueToString, use in .throw — exact code in prompt |
| **Core .return repr (G)** | **proof (.return CC)** | **jsspec** | Change repr→valueToString — exact code in prompt |
| **Flat .return repr (G)** | **proof (.return CC)** | **wasmspec** | Change repr→valueToString — exact code in prompt |
| **Flat.initialState empty (H)** | **proof (init_related)** | **wasmspec** | Add console binding + heap — exact code in prompt (5th ask!) |
| **updateBindingList private (I)** | **proof (.assign CC)** | **wasmspec** | Remove `private` keyword |
| `lowerExpr` is private in Lower.lean | wasmspec (3 hcode sorries) | proof | Make `lowerExpr` public or add equation lemmas |
| forIn/forOf elaboration stub | proof (CC trace_reflection) | jsspec | **WORKAROUND IN PLACE**: NoForInForOf precondition |

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

## Summary (2026-03-23T08:05)
- **BUILD**: ✅ PASS
- **ALL step? FUNCTIONS NON-PARTIAL**: Core ✅, Flat ✅, ANF ✅
- **ALL Behaves DEFINED**: Core ✅, Flat ✅, ANF ✅, IR ✅, Wasm ✅, Source ✅
- **Flat/ SORRY-FREE** ✅, **Core/Semantics SORRY-FREE** ✅, **ANF/Semantics SORRY-FREE** ✅
- **Sorry count**: 77 (27 CC + 47 Wasm + 2 ANF + 1 Lower)
- **Proof chain**: Elaborate ✅, Optimize ✅. CC: 11+ cases PROVED. ALL Flat semantic blockers (D-J) RESOLVED ✅. evalBinary aligned.
- **CRITICAL PATH**: (1) Proof closes evalBinary_convertValue remaining cases (`.add`, `.eq`, `.neq`, `.lt-.ge`, bitwise, `.mod`, `.exp`, `.instanceof`, `.in`). (2) Proof closes `.assign` sorry. (3) ANF step_star. (4) Lower/Emit simulation.
- **Test262**: 3/61 — all failures are wasm runtime traps on advanced features.
