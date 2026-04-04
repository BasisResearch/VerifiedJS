# wasmspec — Close L9063/L9129 compound condition via trivialChain

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## PROGRESS: EXCELLENT. You built HasIfInHead infrastructure (~430 lines), closed if_direct cases for both branches. ANF at 24 sorries. Now close the compound cases.

## STATE: ANF has 24 sorry lines. Your targets: L9063/L9129 (compound condition) and L9064/L9130 (compound HasIfInHead).

## TASK 1: Close L9063 and L9129 — trivialChain_if_condition_steps

L9063 is:
```lean
| _ => sorry -- compound condition: needs trivialChain infrastructure
```

When the if-condition is compound (not lit/var/this), it must be a trivialChain (from normalizeExpr properties). Write:

```lean
private theorem trivialChain_if_condition_steps (c_flat then_ else_ : Flat.Expr)
    (sf : Flat.State) (env heap funcs callStack : ...)
    (htc : trivialChain c_flat)
    (hstep : Flat.step? ⟨.if c_flat then_ else_, env, heap, funcs, callStack⟩ = some (ev, sf')) :
    ∃ steps_to_value, ... -- reduces to .if (lit v) then_ else_
```

**Follow the pattern of `trivialChain_throw_steps`** which already exists and works:
1. Use `lean_local_search "trivialChain_throw_steps"` to find it
2. Copy the structure: fuel-based induction on `trivialChainCost`
3. Key difference: after reducing condition to value, you get `.if (lit v) then_ else_` instead of `.throw (lit v)`
4. The context-stepping lemma you need is `step?_if_ctx` (or similar) — check with `lean_local_search "step?_if"` or `lean_local_search "if_ctx"`

Use `lean_goal` at L9063 to see the exact goal and hypotheses.

## TASK 2: Close L9064 and L9130 — compound HasIfInHead dispatch

L9064 is:
```lean
all_goals sorry -- compound HasIfInHead: needs depth-induction
```

These handle nested `.if` inside compound expressions (seq_left, let_init, etc.). For each HasIfInHead constructor:
- `seq_left`: `.seq (... if ...) b` → one Flat step moves the left side → still has HasIfInHead → IH
- `let_init`: `.let x (... if ...) b` → similar
- etc.

Approach: cases on the HasIfInHead constructor, then for each case show one Flat step preserves the "has if" property and reduces depth. Use the outer `anfConvert_step_star` IH if available, or build a standalone well-founded recursion on expression depth.

Check with `lean_goal` at L9064 — what hypotheses and IHs are in scope?

## TASK 3 (IF TIME): L8850 (let step sim)

If Tasks 1-2 are done, investigate L8850. Needs HasLetInHead infrastructure (similar to HasIfInHead).

## COORDINATE WITH PROOF AGENT
Proof agent is working on L9180 (NoNestedAbrupt_step_preserved) and L8493-8823 (return/await/yield). DO NOT touch those areas.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
