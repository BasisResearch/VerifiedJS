# proof — Prove let/seq/if/tryCatch_step_sim, then compound cases

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

## YOUR IMMEDIATE TASK: let_step_sim (L6431)

yield_step_sim is DONE (decomposed — great work on HasYieldInHead!). Now focus on the 4 remaining monolithic sorries.

### let_step_sim (L6431)
`ANF.step?` on `.let name rhs body`:
- If `rhs` is a trivial that evaluates to a value → step reduces to `body[name := v]`
- Flat source: `normalizeExpr` for `.let` wraps `normalizeExpr rhs` then `normalizeExpr body`
- Key: unfold `ANF.step?` to get the case. The `.let` step evaluates the trivial `rhs`, extends env, continues with `body`.
- For Flat simulation: the source `.let` expression steps to evaluate its RHS sub-expression in the same way.
- Use `normalizeExpr` inversion (what source expression produced `.let`?) — it's from `bindComplex`.

### seq_step_sim (L6452)
`ANF.step?` on `.seq a b`:
- If `a` is a value → step reduces to `b`
- If `a` steps → `.seq a' b` with updated `a'`
- Similar pattern to let.

### if_step_sim (L6473)
`ANF.step?` on `.if cond then_ else_`:
- Evaluates `cond` (a Trivial), branches to `then_` or `else_`
- Flat source: `normalizeExpr` for `.if` produces `.if` with normalized branches
- Key: `evalTrivial` on cond determines branch, then match Flat branch.

### tryCatch_step_sim (L6494)
`ANF.step?` on `.tryCatch body catchParam catchBody finally_`:
- Body steps → tryCatch body steps
- Body throws → catches
- Body is value → resolves
- Map each to corresponding Flat steps.

## PRIORITY 2: Compound cases (depth induction needed)
These are the remaining sorries from await/return/yield decomposition:
```
Await inner value/compound: L5559, L5592, L5603, L5684, L5717, L5728, L5745
hasBreak/ContinueInHead: L5762, L5775
Await flat_arg compound: L5928, L5931
Return compound: L6081, L6084
Await this-none: L6247
Await compound inner_arg: L6254, L6257
Yield compound: L6407, L6410
```

## APPROACH FOR let/seq/if/tryCatch:
1. `lean_goal` at the sorry line to see the exact proof state
2. Unfold `ANF.step?` at `hstep_eq` to see cases
3. For each case, construct matching Flat steps
4. Use `lean_multi_attempt` to test tactic sequences
5. Even partial progress (decomposing 1 sorry into sub-cases) is valuable

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
