# wasmspec — Close L9065/L9127 compound condition + L9066/L9128 HasIfInHead

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## PROGRESS: HasIfInHead infrastructure built. if_direct cases closed. ANF at 24 sorries.

## STATE: Your targets are L9065, L9066, L9127, L9128 (if compound condition + HasIfInHead).

## TASK 1: Close L9065 and L9127 — trivialChain_if_condition_steps

### step?_if_cond_step ALREADY EXISTS at ~L1474. Do NOT rewrite it.

1. Search: `lean_local_search "trivialChain_throw_steps"` — copy that structure exactly.
2. Search: `lean_local_search "step?_if_cond_step"` — this is your context-lifting lemma.
3. Also search for `Steps_if_cond_ctx` near L1829 — this is multi-step lifting.

4. Write `trivialChain_if_condition_steps`:
```lean
private theorem trivialChain_if_condition_steps (c then_ else_ : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (htc : isTrivialChain c = true) :
    ∃ v evs sf_mid,
      Flat.Steps ⟨.if c then_ else_, env, heap, trace, funcs, cs⟩ evs sf_mid ∧
      sf_mid.expr = .if (.lit v) then_ else_ ∧
      evalTrivial env c = .ok v := by
  sorry -- fuel induction, same as trivialChain_throw_steps
```

Even with sorry body, use it at L9065/L9127 to close those sorries.

5. Then fill in the fuel-induction proof following trivialChain_throw_steps EXACTLY:
   - Base: `.lit v` → 0 steps, already done
   - `.var name` → 1 step (env lookup), use `step?_if_cond_step`
   - `.this` → 1 step
   - `.seq a b` → step a to value, drop, recurse on b with IH

## TASK 2: Close L9066 and L9128 — compound HasIfInHead

Use `lean_goal` at L9066 to see what goals remain. Each is a HasIfInHead constructor case.

For each: the `.if` is nested in an expression context (seq, let, etc.). One Flat step on the outer expression steps the context, getting closer to the `.if`. Use depth induction.

Pattern:
```lean
-- HasIfInHead.seq_left: expr = .seq (.if c t e) b
-- Flat.step? steps the .seq, which steps the .if condition
-- IH gives the result at smaller depth
```

## TASK 3 (IF TIME): Close L8856 (let step sim)

## COORDINATE WITH PROOF AGENT
- proof agent works on L9178 (NoNestedAbrupt_step_preserved). DO NOT touch L9178.
- proof agent may edit nearby areas. Check before editing L9170-9200.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
