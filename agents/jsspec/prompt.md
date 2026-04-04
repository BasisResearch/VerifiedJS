# jsspec — TASK 1 IS NOT DONE. DO IT NOW.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 14 sorry tokens. You closed L6673 last run, good. But you STILL have not done Task 1.

## TASK 1 — HIGHEST PRIORITY — DO THIS FIRST — NO EXCUSES

**Switch ALL callers of `convertExpr_not_value` to `convertExpr_not_value_supported`.**

This eliminates L1507 + L1508 (forIn/forOf) for **-2 sorries** with MECHANICAL changes.

### Why this works
`convertExpr_not_value` (around L1502) has no `supported` hypothesis, so forIn/forOf are unprovable sorry.
`convertExpr_not_value_supported` (around L1515) takes `hsupp : e.supported = true` and handles forIn/forOf via contradiction (they're not supported).

### Exact steps:
1. Run `lean_local_search "convertExpr_not_value"` to find ALL call sites
2. At each call site, change `convertExpr_not_value X Y ...` to `convertExpr_not_value_supported X Y hsupp_sub ...`
3. For `hsupp_sub`, derive from the parent's `h_supported` or `hsupp`:
   - If parent has `(.if c t e).supported = true`, get `c.supported = true` via simp
   - If parent has `(.binary op l r).supported = true`, get sub-expression supported via simp
   - Use `Core.Expr.supported` simp lemmas
4. After ALL callers are switched: delete or deprecate the sorry'd `convertExpr_not_value`
5. Verify build passes: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

This is 100% mechanical. No architecture changes. No investigation needed. Just find-and-replace with supported hypotheses.

## TASK 2 (ONLY AFTER TASK 1): Investigate L5148 getIndex string

Use `lean_goal` at L5148. Check if `supported` can exclude string indexing.

## TASK 3 (ONLY AFTER TASK 2): L3719/L3742 CCStateAgree

These may be closable now that you understand CCStateAgree better from the L6673 fix.

## DO NOT:
- Touch L4502, L4510 (semantic mismatch — compiler needs changing)
- Touch L6386 (HeapInj blocked)
- Do architecture analysis instead of Task 1
- Edit ANFConvertCorrect.lean

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
