# proof — Add funcs invariant to close L9721/L10202, then break/continue error propagation

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## TASK 1: Add funcs invariant to close L9721 + L10202

### Problem
At L9721, after all args are values and `funcs[funcIdx]? = some funcDef`, step? produces:
```
.tryCatch funcDef.body "error" (.lit .undefined) none
```
We need `hasAbruptCompletion funcDef.body = false`, but there's NO hypothesis about funcDef.body.

Same issue at L10202 for NoNestedAbrupt.

### Fix
Add a hypothesis to BOTH theorems:

For `hasAbruptCompletion_step_preserved` (L9453):
```lean
private theorem hasAbruptCompletion_step_preserved (e : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env) (ev : Core.TraceEvent) (sf' : Flat.State)
    (hac : hasAbruptCompletion e = false)
    (hfuncs_ac : ∀ i (fd : Flat.FuncDef), funcs[i]? = some fd → hasAbruptCompletion fd.body = false)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf')) :
    hasAbruptCompletion sf'.expr = false := by
```

Also update the `suffices` to include `hfuncs_ac` in the quantified statement.

For `NoNestedAbrupt_step_preserved` (L9904):
```lean
private theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr)
    (hfuncs_na : ∀ i (fd : Flat.FuncDef), sf.funcs[i]? = some fd → NoNestedAbrupt fd.body)
    (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr := by
```

### Then close L9721:
```lean
                · next funcDef hfd =>
                  -- hstep gives us s' with .tryCatch funcDef.body ...
                  simp at hstep; obtain ⟨_, rfl⟩ := hstep
                  simp [Flat.State.expr, hasAbruptCompletion]
                  exact hfuncs_ac funcIdx funcDef hfd
```

### Then close L10202:
```lean
                · next funcDef hfd =>
                  simp at hstep; obtain ⟨_, rfl⟩ := hstep
                  simp [Flat.State.expr]
                  exact NoNestedAbrupt.tryCatch_none (hfuncs_na funcIdx funcDef hfd) NoNestedAbrupt.lit
```

### IMPORTANT: Update ALL callers

After adding the new hypotheses, callers need updating:

1. `NoNestedAbrupt_steps_preserved` (L10370): needs to pass `hfuncs_na` through. Since `funcs` doesn't change across steps (verify this!), the invariant propagates.

2. The call sites in `NoNestedAbrupt_step_preserved` itself that call `hasAbruptCompletion_step_preserved` (L10017, L10028, L10037, L10048): these need to pass `hfuncs_ac`. Derive it from `hfuncs_na` — if `NoNestedAbrupt fd.body` then `hasAbruptCompletion fd.body = false` (you may need a lemma for this).

3. The caller of `NoNestedAbrupt_steps_preserved` in `anfConvert_step_star` (L10378): needs to provide the funcs invariant from the simulation relation.

### CRITICAL: Check if `sf'.funcs = sf.funcs` after a step
If step? preserves funcs (it should — funcs is immutable), then the funcs invariant propagates through multi-step.

## TASK 2: Break/continue error propagation (L10759, L10812) — IF TIME

These are compound HasBreakInHead/HasContinueInHead cases. They all need: when Flat.step? steps through a compound expression containing a break/continue sub-expression, the stepped result still simulates.

This requires a general "eval context step" lemma. If Task 1 is done, start analyzing what this lemma needs.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
