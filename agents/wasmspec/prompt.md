# wasmspec — Close L9063/L9129 compound condition + L9064/L9130 HasIfInHead

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## PROGRESS: EXCELLENT. HasIfInHead infrastructure built (~430 lines). if_direct cases closed. ANF at 24 sorries.

## STATE: ANF has 24 sorry lines. Your targets: L9063/L9129 (compound condition) and L9064/L9130 (compound HasIfInHead).

## TASK 1: Close L9063 and L9129 — trivialChain_if_condition_steps

The if-condition is compound (not lit/var/this). It's a trivialChain. You need to step it down to a value.

### COPY THE EXACT PATTERN FROM trivialChain_throw_steps

1. **FIRST**: Read `trivialChain_throw_steps` fully. Use `lean_local_search "trivialChain_throw_steps"` to find it.
2. Write `trivialChain_if_condition_steps` with the SAME structure:
   - Fuel-based induction on `trivialChainCost c_flat`
   - Base cases: `.lit v` (already a value — 0 steps), `.var name` (1 step), `.this` (1 step)
   - `.seq a b`: case split on `exprValue? a`, value→drop left, non-value→IH
   - Each step uses `step?_if_ctx` to lift the inner step to the `.if` context

3. `step?_if_cond_step` ALREADY EXISTS at L1474! Use it directly:
```lean
-- Signature:
step?_if_cond_step (s : Flat.State) (cond then_ else_ : Flat.Expr)
    (hnotval : Flat.exprValue? cond = none)
    (t : Core.TraceEvent) (sc : Flat.State)
    (hstep : Flat.step? { s with expr := cond } = some (t, sc))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .«if» cond then_ else_ } = some (t, s') ∧
      s'.expr = .«if» sc.expr then_ else_ ...
```
   Also check for `Steps_if_cond_ctx` (multi-step lifting) — search near L1829.

4. The theorem statement should be:
```lean
private theorem trivialChain_if_condition_steps (c then_ else_ : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (htc : isTrivialChain c = true) :
    ∃ v evs sf_mid,
      Flat.Steps ⟨.if c then_ else_, env, heap, trace, funcs, cs⟩ evs sf_mid ∧
      sf_mid.expr = .if (.lit v) then_ else_ ∧
      evalTrivial env c = .ok v := by
```

5. Use this at L9063/L9129 to close the compound condition sorry.

## TASK 2: Close L9064 and L9130 — compound HasIfInHead dispatch

Use `lean_goal` at L9064 to see all goals. Each goal corresponds to a HasIfInHead constructor:
- `seq_left`, `seq_right`, `let_init`, `assign_rhs`, etc.

For each: the expression has `.if` nested inside a context. One Flat step evaluates the context, reducing toward the `.if`. This is a depth-induction argument similar to normalizeExpr_labeled_step_sim.

Pattern for each case:
```lean
-- HasIfInHead.seq_left case: .seq (.if ...) b
-- One flat step: .seq steps because .if is non-value
-- Use IH on (.if ...) at smaller depth
```

## TASK 3 (IF TIME): L8850 (let step sim)
Investigate L8850 after Tasks 1-2.

## COORDINATE WITH PROOF AGENT
Proof agent works on L9180 (NoNestedAbrupt_step_preserved). DO NOT touch L9180.
Proof agent may also work on L8493-8823 (return/await/yield compound). Check sorry comments before editing nearby.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
