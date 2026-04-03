# proof — Close let/if/tryCatch_step_sim, then compound cases

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

## IMPORTANT: SKIP seq_step_sim (L6761) FOR NOW

You correctly identified the while-loop SimRel blocker. The seq case produces
`.seq (.seq d (.while_ c d)) b` after while unrolling, which breaks ANF_SimRel
because normalizeExpr with trivial-preserving k can't produce that form.

**DO NOT spend time on seq_step_sim this run.** Instead, work on the 3 easier theorems.
The seq/while fix requires generalizing ANF_SimRel — that's a separate task.

## YOUR IMMEDIATE TASK: let, if, tryCatch step_sim (3 sorries)

### 1. let_step_sim (L6757) — START HERE, MOST TRACTABLE

Goal: ANF steps `.let name rhs body` → show Flat takes matching steps.

normalizeExpr only produces `.let` from Flat `.let`:
```lean
| .let name init body =>
    normalizeExpr init (fun initTriv =>
      let name' := ... fresh name ...
      normalizeExpr body[name'/name] k >>= fun bodyExpr =>
      pure (.let name' (.trivial initTriv) bodyExpr))
```

Wait — check if this is accurate. Use `lean_hover_info` on normalizeExpr at the `.let` case.

ANF.step? on `.let name rhs body`:
```
| .let name rhs body =>
    match evalComplex env rhs with
    | .ok v => some (.silent, pushTrace {s with expr := body, env := env.insert name v} .silent)
    | .error msg => some (.error msg, pushTrace {s with expr := .trivial .litUndefined} (.error msg))
```

Approach:
1. `lean_goal` at L6757 to see exact state
2. `subst hheap henv` to equate heaps/envs
3. `unfold ANF.step? at hstep_eq` to expand the let case
4. Split on `evalComplex env rhs`:
   - `.ok v`: ev = .silent, sa' has extended env. On Flat side, sf.expr is `.let name init body_flat`. Flat also evaluates init.
   - `.error msg`: Error case, simpler.
5. For Flat side: need `normalizeExpr_let_implies_hasLetInHead` or case-analyze which Flat expressions produce `.let` after normalization.

### 2. if_step_sim (L6827)

normalizeExpr produces `.if cond then_ else_` from Flat `.if`:
```lean
| .if cond then_ else_ =>
    normalizeExpr cond (fun condTriv => do
      let thenExpr ← normalizeExpr then_ k
      let elseExpr ← normalizeExpr else_ k
      pure (.if condTriv thenExpr elseExpr))
```

ANF.step? on `.if cond then_ else_`:
- `evalTrivial env cond` → `.ok v`: branch on `toBoolean v`, result is then_ or else_
- `.error msg`: error

The Flat side `.if cond then_ else_` steps similarly. Key: `cond` in ANF is a Trivial, so evalTrivial always gives a value (for lit) or var lookup.

Approach:
1. Build `normalizeExpr_if_implies_hasIfInHead` (similar to await/return/throw pattern)
2. Case-split on the Flat expression that produced `.if`
3. Show Flat `.if` steps by evaluating the condition and branching

### 3. tryCatch_step_sim (L6848)

Similar pattern. normalizeExpr produces `.tryCatch` from Flat `.tryCatch`. ANF and Flat both step tryCatch by sub-stepping the body.

## PRIORITY 2: Compound cases (after closing the above 3)

These are the `| _ => sorry` patterns in the HasAwaitInHead/HasReturnInHead/HasYieldInHead proofs. Each needs induction on the compound sub-expression. There are ~14 of these.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
- seq_step_sim — blocked on SimRel generalization

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
