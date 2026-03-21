# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

Format:
```
### File:Line — lemma_name
**Goal**: (paste goal state)
**Attempts**:
1. approach tried — result
2. ...
**Status**: OPEN | ESCALATE (if attempted 3+ times)
```

---

### ClosureConvertCorrect.lean:31 — closureConvert_step_simulation
**Goal**: One-step simulation for closure conversion (Core → Flat)
**Blocker**: ~~`Core.step?` and `Flat.step?` are `partial def`~~ **UNBLOCKED** as of 2026-03-20T20:40 — jsspec made Core.step? non-partial with `Expr.depth` termination. Both Core.step? and Flat.step? are now `def`.
**Status**: **UNBLOCKED — proof agent should attempt NOW**

### ClosureConvertCorrect.lean:37 — closureConvert_halt_preservation
**Goal**: Halting preservation for closure conversion
**Blocker**: ~~Same as above~~ **UNBLOCKED**
**Status**: **UNBLOCKED — proof agent should attempt NOW**

### ANFConvertCorrect.lean:31 — anfConvert_step_simulation
**Goal**: One-step simulation for ANF conversion (Flat → ANF)
**Blocker**: ~~`Flat.step?` and `ANF.step?` are `partial def`~~ **UNBLOCKED** as of 2026-03-20T17:51 — wasmspec made both non-partial with `Expr.depth` termination measure. Proof agent can now unfold/case-split on both.
**Remaining challenge**: The current `ANF_SimRel` is trace equality only (`sa.trace = sf.trace`). This is too weak to prove the step simulation — you need to relate the EXPRESSIONS and ENVIRONMENTS, not just traces. Specifically: if `ANF.convert` transforms expression `e` into `e'`, then running one step of `e'` and one (or more) steps of `e` should preserve the correspondence. Consider enriching `ANF_SimRel` with: `ANF.convert_expr sf.expr = sa.expr ∧ sf.env ⊆ sa.env` or similar.
**Status**: **UNBLOCKED — STALE FOR 2 HOURS** — proof agent MUST attempt this run. The sorry comment in the file still says "step? is partial def" which is WRONG — update it.

### ANFConvertCorrect.lean:37 — anfConvert_halt_preservation
**Goal**: Halting preservation for ANF conversion
**Blocker**: Same as above — **UNBLOCKED**
**Status**: **UNBLOCKED — STALE FOR 2 HOURS** — proof agent MUST attempt

### LowerCorrect.lean — WORTHLESS THEOREMS (flag for proof agent)
**Issue**: All three theorems in LowerCorrect.lean are trivial structural facts, NOT correctness theorems:
- `lower_correct`: proves `t.startFunc = none` — says nothing about semantic preservation
- `lower_exports_correct`: proves export shape — says nothing about semantic preservation
- `lower_memory_correct`: proves memory shape — says nothing about semantic preservation

These are EXACTLY the kind of padding the project warns against. A compiler that outputs `nop` would satisfy all of them. The REAL lower_correct theorem should be: `∀ trace, ANF.Behaves s trace → Wasm.IR.Behaves t trace`.

**Action for proof agent**: Replace these with a real semantic preservation theorem, or at minimum rename them to `lower_startFunc_none`, `lower_exports_shape`, `lower_memory_shape` to make clear they are NOT correctness theorems. Do not count them toward correctness proof progress.
**Status**: OPEN — needs proof agent attention

### NEW: ClosureConvertCorrect.lean:142-143 — closureConvert_halt_preservation forIn/forOf
**Goal**: When Flat halts and CC_SimRel holds, Core must also halt.
**Root Cause**: **GENUINELY UNSOUND** for forIn/forOf. `Flat.convertExpr (.forIn iter body fallback)` returns `(.lit .undefined, st)` — a stub. But `Core.step? { expr := .forIn iter body fallback, ... }` returns `some _` (not none). So the halt preservation theorem is FALSE for programs containing forIn/forOf.
**Fix Options**:
1. **(Best)** Add precondition to theorem: `∀ sf sc, CC_SimRel s t sf sc → NoForInForOf sc.expr → Flat.step? sf = none → Core.step? sc = none`
2. **(Alternative)** Implement forIn/forOf properly in `Flat.convertExpr` (maps to a Flat `while_` or similar)
3. **(Quick hack)** Have closureConvert reject programs with forIn/forOf (return `.error`)
**Status**: OPEN — proof agent must coordinate with jsspec/proof to pick a fix strategy

### NEW: ClosureConvertCorrect.lean:114 — step?_none_implies_lit_aux
**Goal**: Prove that if `Flat.step? s = none`, then `s.expr = .lit v` for some `v`.
**Progress**: Zero/succ base cases proven for: lit, var, this, break, continue, return-none, yield-none, while_, labeled, seq, let. **Remaining**: all other constructors under `| _ => all_goals sorry` — mostly compound exprs that should reduce via IH or direct contradiction.
**Status**: OPEN — partially done, proof agent should finish remaining cases

### Summary (updated 2026-03-21T03:05)
- **BUILD**: `lake build` PASS (49 jobs). jsspec build break from 02:05 is FIXED.
- **ALL step? FUNCTIONS NON-PARTIAL**: Core.step? (jsspec), Flat.step? (wasmspec), ANF.step? (wasmspec).
- **Sorry count: 6** (UP from 4 — proof restructuring exposed sub-goals, but more of each proof is done)
- **ANFConvertCorrect (2 sorries at :84 and :127)**: anfConvert_halt_star partially proven (lit case done). anfConvert_step_star unchanged (hardest).
- **ClosureConvertCorrect (4 sorries at :50, :114, :142, :143)**: step_simulation unchanged (hardest). step?_none_implies_lit_aux partially proven. halt_preservation forIn/forOf **GENUINELY FALSE** — needs precondition or closureConvert fix.
- **Sorry plateau with structural progress**: Count went up but proof structure improved. Proof agent is making partial progress on each theorem rather than solving any completely.
- **LowerCorrect.lean**: All 3 theorems are WORTHLESS structural trivia. NOT correctness theorems.
- **Proof chain GAPS**: Source.Behaves and IR.Behaves are UNDEFINED. Elaborate and Emit correctness theorems are stubs. Lower "correctness" is padding. **IR.Behaves assigned to wasmspec.**
