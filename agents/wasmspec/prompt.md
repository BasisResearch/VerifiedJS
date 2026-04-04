# wasmspec — Close remaining ANF sorries: let/while/seq step_sim + inner compound cases

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~100MB available right now.
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: 30 ANF sorry lines remaining

Supervisor just closed objectLit cases in hasAbruptCompletion_step_preserved and NoNestedAbrupt_step_preserved (L9764, L10127 → proved). Equation lemmas for getProp/setProp/getIndex/setIndex/deleteProp now exist in Flat/Semantics.lean.

Proof agent is working on: call/newObj all-values (L9706, L9721, L10070, L10084) and tryCatch (L9779, L10155).

## YOUR TARGETS

### TARGET 1: normalizeExpr_let_step_sim (L9045)

This sorry is about what normalizeExpr produces for `.let name init body`:
```
normalizeExpr (.let name init body) k =
  normalizeExpr init (fun initVar => .let name initVar (normalizeExpr body k))
```

The Flat step is `.let name init' body` where init' is stepped. The ANF side normalizes init, so stepping init on the Flat side corresponds to stepping normalizeExpr init on the ANF side.

Use `lean_goal` at L9045 to get the exact proof state. Then:
1. Unfold `normalizeExpr` to see the structure
2. Apply the SimRel for the init sub-expression
3. Reconstruct SimRel for the result

### TARGET 2: while step_sim (L9135, L9147)

L9135: While condition is a value → step produces `.if cond body+loop .lit`
L9147: While condition is compound → step the condition

For L9147 (condition-steps), the pattern should be straightforward:
- Flat steps the condition in `.while_ cond body`
- ANF normalizes the while, which normalizes the condition first
- The condition step preserves SimRel

### TARGET 3: if compound sorries (L9328-9329, L9401-9402)

L9328: compound condition multi-step
L9329: compound HasIfInHead
L9401-9402: same pattern

These need the eval context stepping lemma for if-conditions. If the condition is compound (not lit/var/this), normalizeExpr recurses into it. The multi-step case needs induction.

### TARGET 4: Inner compound cases (L8677, L8854, L9012)

These are the `| _ => sorry` wildcards where `inner_val` is compound. With `hna : NoNestedAbrupt`, `hasAbruptCompletion inner_val = false`. The approach:
1. `normalizeExpr_X_some_or_k` gives disjunction: HasXInHead or continuation
2. HasXInHead → contradiction with hna
3. Continuation → inner_val is trivial chain

These need `no_X_head_implies_trivial_chain` helpers (throw version exists, need return/await/yield).

## PRIORITY ORDER
1. L9147 (while condition-steps) — most likely closeable
2. L9045 (let step_sim)
3. L9328-9329, L9401-9402 (if compound)

## DO NOT just analyze. WRITE CODE. Close at least 1 sorry line.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
