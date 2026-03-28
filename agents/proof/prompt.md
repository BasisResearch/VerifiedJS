# proof — ANF IS YOUR ONLY PRIORITY

## STATUS: ANF has been sorry for 6+ DAYS. CC can wait. ANF CANNOT.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean` — 13 sorries.

## BREAK/CONTINUE CASE (L172, L174) — EXACT TACTIC SCAFFOLD

I tested these tactics. The following gets you to a clean intermediate goal:

```lean
-- For break (L172):
obtain ⟨_, sa_env, sa_heap, sa_trace⟩ := sa
simp only [] at hsa; subst hsa
simp [ANF.step?] at hstep_eq
obtain ⟨rfl, rfl⟩ := hstep_eq
-- Now: ev = .silent, sa' = ANF.pushTrace {.trivial .litUndefined, sa_env, sa_heap, sa_trace} .silent
-- sa' has expr = .trivial .litUndefined, trace = sa_trace ++ [.silent]
-- Need: ∃ sf' evs, Flat.Steps sf evs sf' ∧ observableTrace [.silent] = observableTrace evs ∧ ANF_SimRel ... ∧ ExprWellFormed ...
```

After this point:
1. `observableTrace [.silent] = []` so you need `observableTrace evs = []`
2. From `hnorm`: `normalizeExpr sf.expr k` produced `.break label`. Invert to learn `sf.expr = .break label` (Flat).
3. Show `Flat.Step sf .silent sf'` where `sf' = {sf with expr := .lit .undefined, trace := sf.trace ++ [.silent]}`
4. Build new `ANF_SimRel s t sa' sf'` — sa'.expr = .trivial .litUndefined, sf'.expr = .lit .undefined
5. For new SimRel k', use `fun t => pure (.trivial t)` (identity continuation) since terminal state

Use `lean_goal` and `lean_multi_attempt` aggressively at each sub-step. The continue case (L174) is identical in structure.

## THROW/RETURN/YIELD/AWAIT (L155, L159, L161, L163)

Same pattern: destructure sa, subst hsa, simp [ANF.step?] at hstep_eq. These have a `Trivial` or `Option Trivial` arg. After simplifying step?, relate to Flat side.

## VAR (L138)

`ANF.step?` on `.var name` does env lookup. After simp [ANF.step?], case split on env lookup result.

## DO NOT TOUCH CC until you close at least 4 ANF sorries.

The CC build may have issues — IGNORE THEM. ANF is the critical path.

## Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
## Log progress to agents/proof/log.md.
