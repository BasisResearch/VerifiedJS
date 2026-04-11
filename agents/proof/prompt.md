# proof — FIX TRIVIAL MISMATCH INFRASTRUCTURE (11 sorries blocked)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T23:30
- ANF: 30 real sorries. CC: 12. Total: **42** (was 44 → -2 this cycle).
- You deleted dead code (break/continue) for -2 last run. GOOD.
- You correctly identified P0 labeled list tail as BLOCKED by **trivial mismatch**.
- The trivial mismatch also blocks L10799-L11022 (6 sorries) and L11024/L11076 (2 more).
- **11 sorries share this ONE blocker.** Fixing it is the highest-leverage task.

## P0: FIX THE TRIVIAL MISMATCH (HIGHEST PRIORITY — 11 sorries)

The problem: `normalizeExpr_labeled_branch_step` needs `normalizeExpr sf'.expr K = body` (exact equality). But when a non-head element `e` (e.g., `.var "x"`) steps to its value (`.lit v`), the trivial changes, so the continuation `k` produces a DIFFERENT body.

### Option A: Use normalizeExpr_labeled_step_sim pattern
`normalizeExpr_labeled_step_sim` (L11176) already handles k' flexibility. Check:
1. `lean_hover_info` on `normalizeExpr_labeled_step_sim` to see its full signature
2. Can the non-head cases in `normalizeExpr_labeled_branch_step` call `normalizeExpr_labeled_step_sim` instead of needing exact body equality?
3. The step_sim theorem produces a NEW body through a different k' — check if this composes with the outer proof

### Option B: Change the theorem statement
Instead of concluding `normalizeExpr sf'.expr k = .ok (.labeled label body, m')`, conclude:
```
∃ body', (normalizeExpr sf'.expr k).run n' = .ok (.labeled label body', m') ∧
  ∀ env heap, ANF.eval body env heap = ANF.eval body' env heap
```
This requires defining and proving semantic equivalence for the body.

### Option C: Two-phase approach
For the non-head case `¬HasLabeledInHead e`:
1. Step `e` to a value (multi-step via IH or direct stepping)
2. After `e` is a value, the list evaluation proceeds to `rest`
3. `rest` still has `HasLabeledInHeadList rest` — recurse on `rest`
4. The BODY is produced by recursion on `rest`, NOT by the continuation applied to `e`
5. So body equality holds because `e` only affects the prefix steps, not the body itself

**CHECK**: Is option C correct? `lean_goal` at L11107 (makeEnv_values case). The body comes from `hnorm : (normalizeExpr (.makeEnv (e :: rest)) k).run n = .ok (.labeled label body, m)`. After stepping `e` to value `v`, the remaining expression is `.makeEnv ((.lit v) :: rest)`. Does `normalizeExpr (.makeEnv ((.lit v) :: rest)) k` produce the SAME `body`? If `k` gets a trivialChain that includes the result of normalizing `e`, and normalizing `.lit v` vs normalizing `e` gives different trivials... then NO.

**START HERE**: `lean_goal` at L11107 to see the exact goal. Then trace through how `normalizeExpr (.makeEnv values) k` threads the trivials. Determine if Option C works.

If Option C fails, try Option A. If Option A fails, implement Option B.

**Expected: Unblock 3-11 sorries if successful.**

## P1: COMPOUND THROW HEAD CASES (L13809) — LOW PRIORITY

Only if P0 is done or fully blocked. The `| _ => sorry` at L13809 covers ~30 HasThrowInHead constructors. Head-position cases (~17) could be proved. But LSP times out in this region.

## DO NOT WORK ON:
- L16451 (wasmspec P2)
- L21749+ (compound cases — all blocked by deeper issues)
- ClosureConvertCorrect.lean

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — P0 trivial mismatch investigation" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
