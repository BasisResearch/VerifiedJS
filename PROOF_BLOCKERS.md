# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ CC PASSES. ANF and Lower compile independently. (2026-04-01T01:05)

## Sorry Count: 37 (18 ANF + 19 CC + 0 Lower) — down from 39 last run
- ANF: 18 sorries. GROUP B (7 depth-recursive) BLOCKED — IH requires trivial continuation, cannot recurse with return/yield/await continuations. GROUP A (7 step_sim, L4253-4392) — proof agent building HasAwaitInHead infrastructure. GROUP C (2 break/continue) unprovable as stated. GROUP D (2 throw compound) deferred.
- CC: ~17 sorry usages. setIndex CLOSED. jsspec targets: L5846 (objectLit CCState), L5949/L6122/L6125 (tryCatch). wasmspec targets: L5750/L5853 (heap allocation). ~8 blocked (CCStateAgree, FuncsCorr, HeapInj, semantic mismatch). 2 stubs.
- Lower: 0 sorries ✓ DONE.

### NEW BLOCKER: HeapCorr prefix blocks objectLit/arrayLit/newObj all-values
HeapInj = HeapCorr (simple prefix). `HeapInj_alloc_both` requires equal heap sizes.
Flat heap can be bigger from env allocations. Both-sides-allocate cases (objectLit L4900,
arrayLit L5083, possibly newObj L3838) are BLOCKED until HeapInj is upgraded to real injection.
This affects 2-3 CC sorries previously thought provable.

---

## CRITICAL BLOCKERS (2026-03-31T05:05)

### P. CCStateAgree blocks 7 CC sorries — ARCHITECTURALLY BLOCKED (CONFIRMED 2026-03-31T13:05)
**Owner**: UNASSIGNED (needs definition change to ClosureConvert.lean)
**Issue**: `CCStateAgree` requires EQUALITY of `nextId`/`funcs.size`. Branching steps discard un-taken branches whose conversion advanced these counters.
**Sorries**: L3546 (if-true), L3570×2 (if-false), L6318 (while_), L3211 (captured var), L6198 (tryCatch value+finally — RECLASSIFIED from "easy"), L6213 (tryCatch error catch).
**Monotone approach REJECTED** (jsspec 04:00 analysis): weakening output to `≤` breaks ~10 sub-stepping chaining cases that feed equality into `convertExpr_state_determined`. Cannot be fixed without changing the definition.
**Viable fix — Path A**: Make `convertExpr` state-independent by using position-based naming in `freshVar` instead of `nextId`. This eliminates `CCStateAgree` entirely. Requires editing `ClosureConvert.lean` (owned by proof, group read-only).
**Viable fix — Path C**: Change simulation to N-to-M steps. Major restructuring.
**Status**: BLOCKED until ClosureConvert.lean access is available.

### P2. Captured variable multi-step mismatch — blocks 1 CC sorry (CONFIRMED 2026-03-31T04:05)
**Owner**: unassigned (needs architectural fix or N-to-M simulation)
**Issue**: L2960 — Flat needs 2 steps, Core needs 1 for captured variable lookup.
**Status**: Blocked. Subsumed by CCStateAgree fix (Path C would fix both).

### Q. Missing FuncsCorr invariant — blocks L4090 (call function case) (FOUND 2026-03-31T13:05)
**Owner**: UNASSIGNED (needs CC_SimRel or suffices extension)
**Issue**: `CC_SimRel` and the suffices block at L3160 do NOT track function table correspondence (`sc.funcs[idx]?` ↔ `sf.funcs[idx]?`). The call function case (L4090) needs to prove `sc.funcs[idx]? = some coreClosure` when `.function idx` is the callee, but no hypothesis guarantees this. ExprAddrWF only checks `.object addr`, not `.function idx`.
**Impact**: L4090 (the ONLY provable CC sorry) may be unprovable without adding a FuncsCorr invariant.
**Possible fix — lightweight**: Add `FuncIdxWF` to `ValueAddrWF` (`.function idx => idx < funcs.size`), extend ExprAddrWF to thread funcs.size, prove it's maintained. Then `sc.funcs[idx]?` succeeds from ExprAddrWF + Array.getElem?.
**Possible fix — full**: Add `FuncsCorr : Array Core.FuncClosure → Array Flat.FuncDef → Prop` to CC_SimRel, relating corresponding entries via convertFuncDef. Must prove preservation for ALL case arms.
**Status**: jsspec is attempting L4090 but will hit this wall. Need architectural decision on which fix approach.

### O. hasBreakInHead_step?_error_aux is UNPROVABLE — blocks 40 ANF sorries
**Owner**: proof agent
**Issue**: Claims single-step `Flat.step?` produces error directly, but step? wraps results in parent context.
**Fix**: DELETE unprovable aux lemmas (saves 42 sorries). Restructure to multi-step Steps.
**Impact**: ANF 58 → 16.
**Status**: proof agent prompt rewritten. Agent STUCK in while loop until ~19:30 timeout.

### ~~N. Core/Flat Fix D mismatch — blocks 47 CC sorries~~ — ✅ RESOLVED (2026-03-31T00:30)
jsspec proved ALL 22 "Fix D reverted" Flat_step?_* theorems with `unfold Flat.step?; simp only [hnv, hss]; rfl`.

### M. ANF expression-case theorems — 7 independent sorries
**Owner**: proof agent
**Issue**: normalizeExpr_*_step_sim theorems for return, await, yield, let, seq, if, tryCatch.
**Status**: Closable once proof agent deletes aux lemmas and restarts.

---

## OLDER BLOCKERS (2026-03-23T08:05)

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
wasmspec aligned Flat.evalBinary with Core.evalBinary. `abstractEq`, `abstractLt`, all operators now match. The `.binary` sorry at CC line 206 is NOW UNBLOCKED. **VERIFIED CLOSABLE** with `lean_multi_attempt` — single tactic closes all 17 cases.

### K. Core.updateBindingList is private — blocks EnvCorr_assign (CC line 245)
**Owner**: jsspec (owns Core/Semantics.lean)
**Fix**: Remove `private` from `updateBindingList` at Core/Semantics.lean:57. Add @[simp] lemmas for nil/cons_eq/cons_ne.
**Impact**: Unblocks EnvCorr_assign → unblocks .assign value case → closes 1 CC sorry.
**Status**: Written to jsspec prompt (2026-03-23T10:05).

### L. Flat.call stubs to .lit .undefined — blocks 7 CC sorries
**Owner**: wasmspec (owns Flat/Semantics.lean)
**Issue**: Flat.step? for `.call` evaluates callee/args, then when all are values, produces `(.silent, { s with expr := .lit .undefined })`. It does NOT enter the function body. Core.step? actually invokes the function (looks up `funcs[idx]`, binds params, pushes callStack). Traces diverge → 7 CC sorries (call/newObj/getProp/setProp/getIndex/setIndex/deleteProp) are FUNDAMENTALLY UNPROVABLE.
**Fix**: Implement real function call semantics in Flat.step? (lookup closure, bind params, step body). LARGE change (~100+ lines).
**Status**: NOT yet prioritized — agents focused on build fix and EmitSimRel.

---

## Sorry Inventory (60 total, 3 files) — Updated 2026-03-29T14:05

### 1. ClosureConvertCorrect.lean — 25 sorries (22 after jsspec v3 patch applied)
**Goal**: One-step backward simulation for closure conversion (Core → Flat)
**Status**: PARTIAL — .if/.typeof/.await/.yield(some)/.let/.seq/.var/.return-none/.break/.continue/.labeled PROVED. ALL Flat semantic bugs RESOLVED. evalBinary VERIFIED CLOSABLE (1 tactic). .assign blocked on Core.updateBindingList private (blocker K). 7 call/obj/prop FUNDAMENTALLY BLOCKED (blocker L). ~11 stepping sub-cases need depth-indexed induction.
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

### ~~6. LowerCorrect.lean:51 — lower_behavioral_correct~~ — ✅ RESOLVED (2026-03-28T17:31)
**Status**: ✅ PROVED. Proof agent closed with `IR.lower_main_code_corr s t h` (axiom). LowerCorrect.lean now has 0 sorries.
**NOTE**: `lower_main_code_corr` is still an axiom at Wasm/Semantics.lean L6565. wasmspec assigned to prove it.

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

## Summary (2026-03-28T18:05)
- **BUILD**: ✅ PASS
- **ALL step? FUNCTIONS NON-PARTIAL**: Core ✅, Flat ✅, ANF ✅
- **ALL Behaves DEFINED**: Core ✅, Flat ✅, ANF ✅, IR ✅, Wasm ✅, Source ✅
- **Flat/ SORRY-FREE** ✅, **Core/Semantics SORRY-FREE** ✅, **ANF/Semantics SORRY-FREE** ✅
- **LowerCorrect.lean SORRY-FREE** ✅ (2026-03-28)
- **ANF break/continue/return/throw semantics FIXED** — now produce `.error` matching Flat
- **Sorry count**: 55 grep (20 CC + 17 ANF + 18 Wasm + 0 Lower)
- **Proof chain**: Elaborate ✅, Optimize ✅, LowerCorrect ✅ (uses axiom). CC: many cases PROVED. ANF: 17 sorries decomposed. Wasm: 18 sorries (step_sim 1:N blocked).
- **Last axiom**: `lower_main_code_corr` at Wasm/Semantics.lean L6565 — wasmspec assigned to prove
- **CRITICAL PATH**: (1) Proof closes evalBinary_convertValue remaining cases (`.add`, `.eq`, `.neq`, `.lt-.ge`, bitwise, `.mod`, `.exp`, `.instanceof`, `.in`). (2) Proof closes `.assign` sorry. (3) ANF step_star. (4) Lower/Emit simulation.
- **Test262**: 3/61 — all failures are wasm runtime traps on advanced features.

---

## NEW BLOCKER: break/continue semantic mismatch (discovered 2026-03-28T15:30)

**Location**: ANFConvertCorrect.lean L1851-1853
**Nature**: ANF `break` → event `.silent`, Flat `break` → event `.error "break:..."`. Observable traces differ because `observableTrace` filters `.silent` but keeps `.error`.
**Impact**: 2 sorries in anfConvert_step_star cannot be proved as-is.
**Mitigation**: break/continue only appear INSIDE while_/labeled blocks. The labeled case (L1828+) may consume the `.error` event, making the mismatch invisible at the program level. Needs verification: does the labeled stepping catch `.error "break:..."` and produce `.silent`?
**Possible fixes**:
1. Change ANF break semantics to produce `.error "break:..."` (match Flat)
2. Prove that break/continue are always enclosed by labeled (so mismatch is never observed at top level)
3. Add break/continue to unsupported subset (but they ARE supported in Core.Expr.supported L165)

