# wasmspec — EXCELLENT WORK ON L4472/4478/4484. Now help with trivialChain.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean

## CONGRATULATIONS: You closed L4472/4478/4484!
The mutual induction bridge theorems are proved. NoNestedAbrupt framework is now fully grounded. This unblocks 5+ sorry closures.

## YOUR TASK: Help close TRIVIAL_CHAIN_IN_THROW (L7487)

proof agent is working on the NoNestedAbrupt-based exfalso closures (P1). You should work on the complementary problem: the ¬HasThrowInHead branch at L7487.

### What L7487 needs
At L7482-7487, we have `¬HasThrowInHead e` and `isTrivialChain e = true` (from `no_throw_head_implies_trivial_chain`). Need to show that `.throw e` Flat-steps to a terminal state matching `ANF.evalTrivial env arg`.

The approach:
1. `isTrivialChain e = true` means `e` is a chain of `.seq(a, b)` / `.var` / `.lit` / `.this` with no compound subexpressions
2. Flat-stepping `.throw e` first steps `e` to a value (since it's trivial), then `.throw (.lit v)` produces an error
3. Need a lemma `trivialChain_steps_to_value`: if `isTrivialChain e = true`, then there exist Flat steps from `e` to `.lit v` where `v` corresponds to `ANF.evalTrivial env (trivialToANF e)`

### What to write:
A helper lemma:
```lean
private theorem trivialChain_throw_steps
    (e : Flat.Expr) (env : Flat.Env) (heap : Core.Heap)
    (trace : List Core.TraceEvent) (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (arg : ANF.Trivial) (n m : Nat)
    (htc : isTrivialChain e = true)
    (hnorm : (ANF.normalizeExpr e (fun t => pure (.throw t))).run n = .ok (.throw arg, m))
    (hewf : ExprWellFormed (.throw e) env) :
    (∀ v, ANF.evalTrivial env arg = .ok v → ∃ evs sf',
      Flat.Steps ⟨.throw e, env, heap, trace, funcs, cs⟩ evs sf' ∧ ...) ∧
    (∀ msg, ANF.evalTrivial env arg = .error msg → ...) := by
```

Use `lean_goal` at L7487 to see the exact goal. Then use `lean_multi_attempt` to test approaches.

### Key sub-cases of trivialChain:
- `e = .lit v`: `.throw (.lit v)` steps directly to error. `normalizeExpr (.lit v) k = k (.lit v)` so `arg = .lit v`.
- `e = .var name`: `.throw (.var name)` steps to `.throw (.lit v)` then to error. `arg = .var name`.
- `e = .this`: Same as var but lookup "this".
- `e = .seq a b`: First step `a` to value (ignored), then continue with `.throw b`.

### COORDINATE WITH PROOF AGENT
proof agent is adding NoNestedAbrupt to theorem signatures (modifying L7460-7613 area). Your work at L7487 should NOT conflict since you're adding a new helper BELOW L7487 and replacing the sorry. If proof agent has already touched L7487, check `git diff` first.

## IF TRIVIALCHAIN IS BLOCKED: Work on L8123 (let step sim) or L8202/L8205 (if step sim)
These are independent sorries that don't need NoNestedAbrupt.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
