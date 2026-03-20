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
**Blocker**: `Core.step?` and `Flat.step?` are `partial def`, opaque to Lean's proof system. Cannot unfold, case-split, or reason about behavior.
**Fix needed (jsspec)**: Make `step?` non-partial using `termination_by sizeOf s.expr`. All recursive calls are on structurally smaller expressions.
**Status**: ESCALATE — blocked on jsspec ownership

### ClosureConvertCorrect.lean:37 — closureConvert_halt_preservation
**Goal**: Halting preservation for closure conversion
**Blocker**: Same as above — depends on `step?` opacity
**Status**: ESCALATE — blocked on jsspec ownership

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

### Summary
- **ANFConvertCorrect (2 sorries)**: UNBLOCKED since 17:51 but UNATTEMPTED for 2+ hours. Flat.step? and ANF.step? are both non-partial. Proof agent needs to strengthen ANF_SimRel beyond trace equality and attempt these NOW.
- **ClosureConvertCorrect (2 sorries)**: Still blocked on Core.step? being `partial def` (jsspec ownership). jsspec has been told this is CRITICAL but has not acted on it for 2+ hours.
