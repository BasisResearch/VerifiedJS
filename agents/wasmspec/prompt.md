# wasmspec — USE the HasIfInHead infrastructure to CLOSE sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## PROGRESS: You built excellent HasIfInHead infrastructure (~430 lines) and closed 3 mutual induction sorries. Now USE IT.

## STATE: ANF has 24 sorry lines. Your targets: L9116/L9117 and L9235/L9236 (if step sim compound).

### Current sorry structure at if step sim:
- **L9116**: `| _ => sorry` — compound condition in `HasIfInHead.if_direct` (true branch)
- **L9117**: `all_goals sorry` — compound HasIfInHead: seq_left, let_init, etc. (true branch)
- **L9235**: `| _ => sorry` — compound condition (false branch, mirror of L9116)
- **L9236**: `all_goals sorry` — compound HasIfInHead (false branch, mirror of L9117)

## TASK 1: Close L9116 and L9235 — compound condition trivialChain

When the condition `c_flat` is compound (not lit/var/this) in `HasIfInHead.if_direct`:
1. The condition must be a trivialChain (from normalizeExpr properties)
2. Write `trivialChain_if_condition_steps`: reduces compound condition to a value via trivialChain stepping
3. Then the `.if (lit v) then else` can step to the appropriate branch

Pattern to follow — `trivialChain_throw_steps` already exists and works:
```lean
-- Search for it:
lean_local_search "trivialChain_throw_steps"
-- Adapt the same pattern: fuel-based induction on trivialChainCost
-- Key difference: after reducing condition to value, step the .if instead of .throw
```

Use `lean_goal` at L9116 to see the exact goal and available hypotheses.

## TASK 2: Close L9117 and L9236 — compound HasIfInHead dispatch

These handle nested `.if` inside compound expressions (seq_left, let_init, etc.).

Approach: The compound expression takes one Flat step → resulting expression still has HasIfInHead → by IH from the outer context (anfConvert_step_star), the proof follows.

Use `lean_goal` at L9117 to check:
- Is there a depth IH in scope?
- What HasIfInHead constructor is in the goal?
- Can you dispatch by cases on HasIfInHead?

If no depth IH: you may need to restructure as a separate `normalizeExpr_if_step_sim_compound` theorem with explicit Well-founded recursion on expression depth.

## TASK 3 (IF TIME): L8850 (let step sim)

Needs HasLetInHead infrastructure (similar to HasIfInHead you just built). If you can build it quickly (~200 lines), do it.

## COORDINATE WITH PROOF AGENT
Proof agent is working on L9409 (NoNestedAbrupt propagation) and L8493-8823 (return/await/yield trivialChain). DO NOT touch those areas.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
