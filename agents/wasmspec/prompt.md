# wasmspec — Close ANF step sim sorries: let, if compound

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.8GB available right now.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9453-9469 (hasAbruptCompletion_step_preserved, NoNestedAbrupt_step_preserved)
- **YOU** work on L9050, L9333/9334, L9406/9407 ONLY
- DO NOT touch lines 9453-9500

## STATUS: Flat/Semantics.lean is DONE. step?_preserves_funcs proved. Focus ONLY on ANF sorry closures.

## YOUR TARGETS (6 sorries)

| Line | What | Difficulty |
|------|------|------------|
| L9050 | let step sim | Medium |
| L9333 | if compound condition (first if) | Medium |
| L9334 | HasIfInHead (first if) | Medium |
| L9406 | if compound condition (second if) | Medium |
| L9407 | HasIfInHead (second if) | Medium |

## TASK 1: Close L9050 (let step sim) — HIGHEST PRIORITY

Use `lean_goal` at L9050 to see the exact proof state.

The proof state after L9046-9047 should have:
- `hstep_eq` decomposed: sa' has body with extended env
- Need to find flat steps that simulate

Pattern: normalizeExpr on `.let name init body` produces nested let/bind structure.
When ANF steps by evaluating the rhs (evalComplex), the flat form should step through the normalized init to a value, then substitute into the normalized body.

Use `lean_hover_info` on the normalizeExpr definition for the let case to understand the target structure.

## TASK 2: Close L9333/9334 + L9406/9407 (if compound)

Use `lean_goal` at L9333 to see what's needed.

Pattern for L9333 (compound condition):
- ANF has `.if cond then_ else_` where cond is not a value and not labeled
- ANF.step? steps within cond to get cond'
- Need: flat steps within normalizeExpr of the if, stepping the normalized condition

Check if there's already a `normalizeExpr_if_decomp` helper or if you need to create one.

For L9334 (HasIfInHead): check what constructors HasIfInHead has and handle each.

## PRIORITY ORDER
1. L9050 (let step sim) — most tractable
2. L9333/9334 (first if compound) — once you have the pattern, L9406/9407 is copy-paste

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
