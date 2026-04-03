# proof — Close let/seq/if/tryCatch_step_sim, then compound cases

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 22 sorries. Lower 0 ✓. CC — OTHER AGENTS OWN IT.

## YOUR IMMEDIATE TASK: 4 monolithic sorries (let/seq/if/tryCatch)

### 1. seq_step_sim (L6453) — START HERE, EASIEST

Goal state (verified 2026-04-03):
```
hnorm : normalizeExpr sf.expr k produces .seq a b
hstep_eq : ANF.step? { expr := .seq a b, env := sa_env, heap := sa_heap, trace := sa_trace } = some (ev, sa')
⊢ ∃ sf' evs, Flat.Steps sf evs sf' ∧ observableTrace [ev] = observableTrace evs ∧ ANF_SimRel s t sa' sf' ∧ ExprWellFormed sf'.expr sf'.env
```

Key insight: Only `.while_` in normalizeExpr produces `.seq` (line 109 of Convert.lean):
```lean
| .while_ cond body => do
    let condExpr ← normalizeExpr cond ...; let bodyExpr ← normalizeExpr body ...
    let rest ← k .litUndefined
    pure (.seq (.while_ condExpr bodyExpr) rest)
```

So `sf.expr` must be `.while_` or something that delegates to while_. ANF.step? on `.seq a b`:
- If `exprValue? a = some v` → steps to `b` with `.silent`
- If `a` steps → `.seq a' b`

Approach:
1. `unfold ANF.step? at hstep_eq; simp at hstep_eq`
2. Split on `exprValue? a`:
   - `some v`: Then `ev = .silent`, `sa' = pushTrace {... expr := b} .silent`. Need to show Flat takes matching steps.
   - `none`: Then there exists `(t, sa)` with `ANF.step? {expr := a} = some (t, sa)` and result is `.seq sa.expr b`. Use IH or structural argument.
3. For the Flat side: `.while_` in Flat steps via `Flat_step?_while`.

### 2. let_step_sim (L6432)

normalizeExpr of `.let name init body` produces `.let name (.trivial initTriv) bodyExpr`.
ANF.step? on `.let name rhs body` immediately evaluates `rhs` via `evalComplex` — always steps.

Approach:
1. `lean_goal` at L6432
2. `unfold ANF.step? at hstep_eq` — `.let` case always succeeds
3. The step evaluates `evalComplex` on `rhs`, extends env with result, continues with `body`
4. On Flat side: `sf.expr` is `.let name init body_flat`. Flat also steps its let by evaluating init.
5. Use `step?_let` theorem from ANF/Semantics.lean:542 to simplify

### 3. if_step_sim (L6474)

normalizeExpr of `.if cond then_ else_` produces `.if condTriv thenExpr elseExpr`.
ANF.step? on `.if cond then_ else_`:
- `evalTrivial env cond` returns `.ok v` → branch on `toBoolean v`
- Or `.error msg`

Approach: unfold `ANF.step?`, split on `evalTrivial` result, match to Flat `.if` stepping.

### 4. tryCatch_step_sim (L6495)

normalizeExpr of `.tryCatch body catchParam catchBody finally_` produces `.tryCatch bodyExpr catchParam catchExpr finallyExpr`.
ANF.step? on `.tryCatch`: sub-steps body, catches throws, resolves values.

## PRIORITY 2: Compound cases (18 remaining sorries)
```
Await inner value/compound: L5559, L5592, L5603, L5684, L5717, L5728, L5745
hasBreak/ContinueInHead: L5762, L5775
Await flat_arg compound: L5928, L5931
Return compound: L6081, L6084
Await this-none: L6247
Await compound inner_arg: L6254, L6257
Yield compound: L6408, L6411
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
