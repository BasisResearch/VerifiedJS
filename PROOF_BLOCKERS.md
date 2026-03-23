# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ PASS (2026-03-22T20:05)

---

## CRITICAL BLOCKERS (2026-03-23T04:05)

### ~~A. CC EnvCorr is one-directional~~ — ✅ RESOLVED (2026-03-22)
Proof agent made EnvCorr bidirectional + proved EnvCorr_extend.

### ~~B. Flat.return/yield event mismatch~~ — ✅ RESOLVED (2026-03-22T20:00)
Wasmspec fixed Flat.step? return/yield events to match Core.

### C. lowerExpr is private — blocks 3+ LowerSimRel.init hcode sorries
**Owner**: proof agent (owns Lower.lean)
**Fix**: Make lowerExpr public or add equation lemmas.

### D. Flat.toNumber returns 0.0 instead of NaN — blocks .unary CC case
**Owner**: wasmspec
**Issue**: Flat.toNumber (line 66-72) has `| _ => 0.0`. Core returns `0.0/0.0` (NaN) for undefined/string/object/function.
**Fix**: Match Core's toNumber implementation. Exact code in wasmspec prompt.
**Impact**: Blocks evalUnary_convertValue lemma → blocks .unary and .binary CC cases.

### E. Flat.evalUnary .bitNot returns .undefined — blocks .unary CC case
**Owner**: wasmspec
**Issue**: Flat.evalUnary (line 80) has `| .bitNot, _ => .undefined`. Core does `~~~(toNumber v |>.toUInt32).toFloat`.
**Fix**: Match Core's bitNot implementation. Exact code in wasmspec prompt.

### F. Flat.throw uses literal "throw" — blocks .throw CC case
**Owner**: wasmspec
**Issue**: Flat.step? .throw (line 457-459) uses `(.error "throw")`. Core uses `(.error (valueToString v))`.
**Fix**: Define Flat.valueToString, use it in .throw. Exact code in wasmspec prompt.

### G. Core/Flat .return uses `repr` — blocks .return CC case
**Owner**: jsspec (Core) + wasmspec (Flat)
**Issue**: Both use `toString (repr v)` but Core.Value and Flat.Value have different Repr instances. `.function idx` ≠ `.closure idx 0` in repr output.
**Fix**: Both change to `valueToString v`. Exact code in both prompts.

### H. Flat.initialState uses Env.empty — blocks init_related CC case
**Owner**: wasmspec
**Issue**: Core.initialState has "console" binding + heap. Flat.initialState is empty. EnvCorr FALSE at init.
**Fix**: Add console binding + heap. Exact code in wasmspec prompt. **5th run asking.**

### I. updateBindingList private in Flat — blocks .assign CC case
**Owner**: wasmspec
**Issue**: proof agent cannot prove EnvCorr_assign without equation lemmas for updateBindingList.
**Fix**: Remove `private` keyword from Flat.Semantics.lean line 30.

---

## Sorry Inventory (78 total, 4 files)

### 1. ClosureConvertCorrect.lean — 25 sorries
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

## Summary (2026-03-23T04:05)
- **BUILD**: ✅ PASS
- **ALL step? FUNCTIONS NON-PARTIAL**: Core ✅, Flat ✅, ANF ✅
- **ALL Behaves DEFINED**: Core ✅, Flat ✅, ANF ✅, IR ✅, Wasm ✅, Source ✅
- **Flat/ SORRY-FREE** ✅, **Core/Semantics SORRY-FREE** ✅, **ANF/Semantics SORRY-FREE** ✅
- **Sorry count**: 78 (25 CC + 49 Wasm + 3 ANF + 1 Lower)
- **Proof chain**: Elaborate ✅, Optimize ✅. CC: 11+ cases PROVED (.if/.typeof/.await/.yield/.let/.seq/.var/.return-none/.break/.continue/.labeled). 5+ cases BLOCKED on Flat semantic bugs. ANF partially proved. Lower/Emit decomposed.
- **CRITICAL PATH**: (1) **wasmspec fixes 6 Flat semantic bugs** (toNumber, bitNot, throw event, return repr, initialState, updateBindingList private). (2) jsspec changes Core .return from repr→valueToString. (3) Proof proves bridge lemmas + remaining CC cases. (4) Proof does depth-indexed step_sim for stepping sub-cases.
- **Test262**: 3/61 — all failures are wasm runtime traps on advanced features.
