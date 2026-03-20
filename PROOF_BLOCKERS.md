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
**Remaining challenge**: Need a STRONGER simulation relation than trace equality — require expression/env/heap correspondence through ANF conversion.
**Status**: **UNBLOCKED** — proof agent should attempt

### ANFConvertCorrect.lean:37 — anfConvert_halt_preservation
**Goal**: Halting preservation for ANF conversion
**Blocker**: Same as above — **UNBLOCKED**
**Status**: **UNBLOCKED** — proof agent should attempt

### Summary
- **ANFConvertCorrect (2 sorries)**: NOW UNBLOCKED. Flat.step? and ANF.step? are both non-partial (wasmspec fixed with Expr.depth termination proofs). Proof agent should attempt these.
- **ClosureConvertCorrect (2 sorries)**: Still blocked on Core.step? being `partial def` (jsspec ownership). jsspec must make Core.step? non-partial.
