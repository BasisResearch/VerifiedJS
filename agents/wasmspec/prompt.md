# wasmspec — if_branch provable cases + K-mismatch architecture

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~800MB free. USE LSP ONLY — no builds. DO NOT launch lean_build.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11638+ (compound cases), L12281+ (while), L16013+ (tryCatch), L17117+ (callframe/break)
- jsspec may work on list cases (L10248, L10297, L10328, L10360, L10391)
- **YOU** own L13901+ and L14996+ ONLY (if_branch zones)

## ===== K-MISMATCH STATUS =====

Your `normalizeExpr_trivialChain_apply` lemma (L1466-1493) was a great contribution. However, the K-mismatch is confirmed UNSATISFIABLE for second-position cases. The `body` parameter is load-bearing through anfConvert_step_star → normalizeExpr_labeled_step_sim → normalizeExpr_labeled_branch_step → normalizeExpr_if_branch_step. Existentially quantifying body' would require refactoring the entire chain.

**The 14 second-position sorry cases (7 per theorem) CANNOT be proved without theorem redesign.** Do not spend more time on them.

## ===== YOUR PRIORITY: ARCHITECTURAL INVESTIGATION =====

### P0: Design the ANF_SimRel weakening (RESEARCH ONLY, no code changes yet)

The fundamental issue: `ANF_SimRel` (around L114-121) requires:
```
(ANF.normalizeExpr sf.expr k).run n = Except.ok (sa.expr, m)
```
This means `sa.expr` is EXACTLY the output of normalizeExpr. When flat stepping changes a `.var x` to `.lit v`, the normalizeExpr output changes (trivialOfFlat(.var x) = .var x ≠ trivialOfFlatValue v).

**Investigate**: Can ANF_SimRel be changed to allow the ANF body to contain `.var x` while the flat state has `.lit (env[x])`? This would require:
1. A "trivial equivalence" relation on ANF.Expr: body ~ body' iff they differ only in trivials that agree under the current environment
2. Showing that ANF stepping preserves this equivalence
3. Showing that the final behavior (trace) is unchanged

**Write your analysis** to agents/wasmspec/k_mismatch_analysis.md. Include:
- Exact definition of proposed weaker SimRel
- Which theorems would need to change
- Estimated number of lines affected
- Whether this is feasible in < 1 day of work

### P1: Close list cases in if_branch (5 per theorem = 10 total)

The list cases (call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems) may be partially provable using the same Classical.em approach as jsspec used in labeled_branch_step. Even proving the first-position sub-case would be progress.

Your sorries:
```
if_branch_step: L13927 call_args, L13976 newObj_args, L14075 makeEnv_values, L14076 objectLit_props, L14077 arrayLit_elems
if_branch_step_false: L15022 call_args, L15071 newObj_args, L15170 makeEnv_values, L15171 objectLit_props, L15172 arrayLit_elems
```

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
