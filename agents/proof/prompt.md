# proof — Close hasBreakInHead/hasContinueInHead, then compound sorries

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` entirely.

## STATE: normalizeExpr_if_cond_source is DONE ✓ (L2025-2468 fully proved).
## ANF has 23 sorries remaining, ALL in L6400-7452 (step simulation cases).

## YOUR IMMEDIATE TASKS (in order):

### TASK 1: hasBreakInHead_flat_error_steps (L6650) — MOST TRACTABLE
This theorem says: if `HasBreakInHead e label`, then `e` flat-steps to `.lit .undefined` with an error trace.

Approach — induction on `h : HasBreakInHead e label`:
- Each constructor of HasBreakInHead tells you which sub-expression has the break
- For `HasBreakInHead.break_`: base case, `e = .break label`. Flat.step? on break produces error directly. Use `Flat.Steps.tail` + `Flat.Steps.refl`.
- For `HasBreakInHead.seq_left b rest hb`: `e = .seq b rest` where `HasBreakInHead b label`. By IH on b, get `sf'` with `.lit .undefined`. Then `.seq (.lit .undefined) rest` steps to `.lit .undefined`.
- For constructors like `return_some_arg`, `throw_arg`, etc.: inner expression has break. By IH, inner steps to `.lit .undefined`. Then outer expression with `.lit .undefined` inside resolves.

Key: structural induction on `HasBreakInHead`, NOT on `e`. Each case: IH → flat steps for sub-expression → show outer steps via Flat.step?.

Use `lean_goal` at L6650 first. Then use `lean_multi_attempt` to test:
```
["induction h with | break_ => ... | seq_left b rest hb ih => ...", "cases h"]
```

### TASK 2: hasContinueInHead_flat_error_steps (L6663) — SAME PATTERN
Identical structure to hasBreakInHead but for `HasContinueInHead`. Copy the proof.

### TASK 3: "non-labeled inner value" sorries (L6447, L6480, L6572, L6605)
These are catch-all `| _ => sorry` cases after labeled is handled. Check what constructors remain.
Use `lean_goal` at each sorry to see exact goal. Try `lean_multi_attempt` with:
```
["contradiction", "simp [*] at *", "omega", "exact absurd ‹_› ‹_›"]
```

### TASK 4: compound/bindComplex sorries (L6491, L6616, L6633)
These say "needs induction on depth". Need depth induction to show simulation.

### SKIP THESE:
- L7326 (.let characterization) — bindComplex PRODUCES .let, approach wrong
- ClosureConvertCorrect.lean — other agents own it

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
