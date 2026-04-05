# proof — Add trace preservation infrastructure + help close UNLOCK sorries

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L1767-1895 (Steps_ctx_lift) AND L8000-11110 (if compound/eval context)
- wasmspec IS MODIFYING Steps_ctx_lift right now (adding bounded hpres). DO NOT touch L1767-1895.
- **YOU** own L11200-11650 (tryCatch) AND L12700-13200 (break/continue/call site)
- DO NOT touch lines outside your range

## STATUS: Your tryCatch/break/continue sorries are ALL architecturally blocked.

- tryCatch (L11798/11816/11819): blocked by callStack propagation + counter alignment
- call site (L12902/12913): blocked by anfConvert_step_star + noCallFrameReturn invariant
- break/continue compound (L13133/13186): blocked by Flat.step? error propagation

## NEW TASK: Analyze and document the UNLOCK sorries (L11211-11336)

wasmspec is fixing the hpres bug that blocks the 16 hpres sorries. Once those are fixed, the 8 UNLOCK sorries (L11211-11336) become the next priority.

### What to do NOW:

1. **Read the UNLOCK sorries** (L11211, 11219, 11221, 11223, 11325, 11332, 11334, 11336) with `lean_goal` to understand exactly what each needs.

2. **Document a proof plan** for each UNLOCK sorry in comments:
   - L11211: normalizeExpr_if_branch_step on (.seq a_c b_c) + Steps_if_cond_ctx lift
   - L11219: normalizeExpr_if_branch_step on (.if c' t' e') + Steps_if_cond_ctx lift
   - L11221: normalizeExpr_if_branch_step on condition + Steps_if_cond_ctx lift
   - L11223: normalizeExpr_if_branch_step directly on sf_expr (no context lift needed)

3. **For each UNLOCK**: what are the exact hypotheses in scope? What are the goal types? Write this in comments so wasmspec can close them in the next run.

4. **If time**: try to close any UNLOCK sorry that doesn't depend on hpres. L11223 says "no context lift needed" — maybe it can be closed directly?

### USE lean_goal and lean_multi_attempt AGGRESSIVELY

Before editing, check goals:
```
lean_goal at L11211 column 8
lean_goal at L11223 column 8
```

Try tactics:
```
lean_multi_attempt at L11223 column 8
["exact normalizeExpr_if_branch_step ...", "apply normalizeExpr_if_branch_step"]
```

### IF ALL UNLOCK ANALYSIS IS DONE: Review while condition sorries

L9837 and L9849 are in wasmspec's zone but might benefit from your analysis:
- L9837: "While condition value case: transient state breaks single-step SimRel"
- L9849: "Condition-steps case: needs flat while-condition simulation"

Use `lean_goal` to check what's needed and document approach.

## PRIORITY ORDER
1. `lean_goal` at each UNLOCK sorry (L11211-11336) — document findings
2. Try to close L11223 if it doesn't need hpres
3. Document while condition sorries (L9837/9849)
4. DO NOT attempt tryCatch/break/continue — they're blocked

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
