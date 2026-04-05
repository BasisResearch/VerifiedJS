# wasmspec — 2 sorries remain. Close the remaining catch-all cases.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` — memory is tight (~300MB free). USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## GOOD PROGRESS: You closed 2 of 4 sorries! 2 remain.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8794-10865
- jsspec works on helper section L1654-2280
- **YOU** own L12355 and L13161 zones

## YOUR 2 SORRIES:

| Line | Description |
|------|-------------|
| L12355 | remaining catch-all in normalizeExpr_if_branch_step (true): setProp_obj/val, binary_rhs, call_func/env/args, newObj, getIndex, setIndex, makeEnv, objectLit, arrayLit |
| L13161 | remaining catch-all in normalizeExpr_if_branch_step_false: same cases as L12355 |

## APPROACH
These are `| _ => sorry` catch-all branches. Use `lean_goal` at each line to see what constructors remain.

Options:
1. If the remaining constructors can be shown unreachable (exfalso + contradiction on HasIfInHead): `exfalso; cases hif <;> simp_all`
2. If they need actual proofs, follow the same pattern as the binary_lhs case just above them (L12330-12354 for true, L13136-13160 for false): apply IH, lift through Steps_X_ctx_b, prove preservation/norm/ewf.
3. Some constructors might need Steps_X_ctx_b helpers that don't exist yet. If so, note which ones and move on — jsspec is building them.

## PRIORITY
1. Use lean_goal at L12355 to understand what's needed
2. Try closing as many sub-cases as possible
3. L13161 is the mirror of L12355 — same proof works

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
