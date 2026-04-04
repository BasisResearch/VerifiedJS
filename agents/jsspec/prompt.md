# jsspec — Eliminate false sorries, then CCStateAgree architecture

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 14 sorry tokens.

### Sorry classification:
- **False theorem (2)**: L1507, L1508 (forIn/forOf in `convertExpr_not_value`) — FIXABLE, see Task 1
- **Unprovable (1)**: L5148 (getIndex string) — investigate
- **Semantic mismatch (2)**: L4502, L4510 (newObj non-value) — DO NOT TOUCH
- **CCStateAgree blocked (6)**: L3719, L3742, L6543, L6544, L6616, L6724
- **HeapInj blocked (1)**: L6386 (functionDef)
- **FuncsCorr blocked (1)**: L4296 (non-consoleLog call)
- **Multi-step blocked (1)**: L3391 (captured var)

## YOUR TASKS (priority order)

### TASK 1: Eliminate L1507 + L1508 by switching to `convertExpr_not_value_supported`

The sorry'd theorem `convertExpr_not_value` (L1502) does NOT have a `supported` hypothesis, so forIn/forOf cases are unprovable. But there's already a proved version `convertExpr_not_value_supported` (around L1515) that takes `hsupp : e.supported = true` and handles forIn/forOf via contradiction.

**Plan**: Switch all callers of `convertExpr_not_value` to `convertExpr_not_value_supported`. Each caller is inside the main simulation theorem which has `h_supported` in scope. You need to:

1. `lean_local_search "convertExpr_not_value"` to find all call sites
2. At each site like `convertExpr_not_value cond hcev scope envVar envMap st`, change to `convertExpr_not_value_supported cond hcev hsupp_cond scope envVar envMap st` where `hsupp_cond` derives from the parent's `supported` hypothesis.
3. For sub-expressions, use `Core.Expr.supported` simp lemmas: if `(.if c t e).supported = true` then `c.supported = true ∧ t.supported = true ∧ e.supported = true`.

Once ALL callers are switched, delete the sorry'd `convertExpr_not_value` or mark it deprecated.

This gives **-2 sorries** with purely mechanical changes.

### TASK 2: Investigate L5148 (getIndex string unprovable)

Use `lean_goal` at L5148 to understand the exact goal. The comment says "getIndex string both-values: UNPROVABLE." Check if `supported` can exclude this case. If the getIndex operation on strings depends on `Float.toString` being opaque, this may need `supported` to exclude string indexing.

### TASK 3: If time, attempt L6616 (tryCatch body-error CCStateAgree)

Use `lean_goal` at L6616. Check if `convertExpr_state_determined` can close it (you used this for L6673). If the CCStateAgree input is the issue, this is architecturally blocked.

### TASK 4: CCStateAgree architecture analysis (ANALYSIS ONLY)

Write a concrete proposal (< 30 lines) to agents/jsspec/log.md:
1. Can we make CCState's nextId deterministic by using expression-path-based naming?
2. Alternative: can we prove that both branches of if/while produce the same nextId delta?
3. How many theorems would break with each approach?

## DO NOT:
- Touch L4502, L4510 (semantic mismatch — compiler needs changing)
- Make architectural changes without supervisor approval
- Edit ANFConvertCorrect.lean

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
