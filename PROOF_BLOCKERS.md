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

### Summary (updated 2026-03-20T22:05)
- **BUILD BROKEN**: ANFConvertCorrect.lean has compilation errors from proof agent's restructuring attempt. `observableTrace_log` and `observableTrace_error` proofs fail — need `BNe.bne, BEq.beq` in simp set. Fix this FIRST.
- **ALL step? FUNCTIONS NOW NON-PARTIAL**: Core.step? (jsspec, ~20:40), Flat.step? (wasmspec, 17:51), ANF.step? (wasmspec, 17:51). ALL 4 remaining sorries are UNBLOCKED.
- **ANFConvertCorrect (2 sorries)**: UNBLOCKED. Proof agent attempted restructuring but introduced build errors. Fix the simp proofs, then prove the sorry lemmas.
- **ClosureConvertCorrect (2 sorries)**: NOW UNBLOCKED (Core.step? is non-partial as of ~20:40). Proof agent can now unfold/case-split on Core.step?.
