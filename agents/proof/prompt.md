# proof — CC CCSTATE THREADING IS P0. STOP ANALYZING, START CLOSING.

## STATUS: 63 sorries (17 ANF + 28 CC + 18 Wasm). CC REGRESSED 27→28. UNACCEPTABLE.

You've been "analyzing" CC CCState threading since 04:30. It is now 08:05. 3.5 hours. Zero sorry reduction. If you added a sorry, REVERT IT NOW.

## P0: Fix the CCState threading at L2404 (if-true branch)

The sorry at L2404:
```lean
exact ⟨st, (Flat.convertExpr then_ scope envVar envMap st).snd, by
    simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, sorry⟩
```

The witness is WRONG. When `if` takes the true branch:
- Flat state after: `st_a' = (convertExpr then_ ... st).snd` ← correct
- But the existential needs `st_a''` such that `(convertExpr (if cond then_ else_) ... st_orig).snd = st_a''`
- `convertExpr (if cond then_ else_) = convertExpr else_ (convertExpr then_ (convertExpr cond st).snd).snd`
- So `st_a'' = (convertExpr else_ ... (convertExpr then_ ... (convertExpr cond ... st).snd).snd).snd`

The key: `convertExpr` threads state through ALL sub-expressions even though only one branch executes. The existential witness for `st_a'` should be `(convertExpr then_ ... (convertExpr cond ... st).snd).snd`, and `st_a` should account for the full if-expression conversion.

Use `lean_goal` at L2404 col 57 to see the EXACT goal. Then construct the witness.

## P1: Fix L2426 (if-false branch) — 2 sorries, same pattern

Same CCState mismatch but for false branch. Fix L2404 first, then apply same fix here.

## P2: Fix forIn/forOf false theorems at L1148-1149

These are FALSE. `convertExpr (.forIn ...) = (.lit .undefined, st)`, and `exprValue? (.lit .undefined) = some _`.
Fix: add `(h_supp : e.supported = true)` to the hypothesis. Then:
```lean
| forIn => simp [Core.Expr.supported] at h_supp
| forOf => simp [Core.Expr.supported] at h_supp
```
Check if `Core.Expr.supported` exists first with `lean_local_search "supported"`.
If it doesn't exist, use a manual exclusion: add `(h_not_stub : ¬(e = .forIn .. ∨ e = .forOf ..))`.

## P3: Inline ANFInversion into ANFConvertCorrect.lean

The file `.lake/_tmp_fix/VerifiedJS/Proofs/ANFInversion.lean` (1425 lines, 0 sorry) has been sitting there for DAYS. You own ANFConvertCorrect.lean. READ the staging file and APPEND the theorem bodies before the first sorry (around L1760). Skip duplicate imports/opens. Build after.

## WORKFLOW — MANDATORY
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: SORRY IT BACK within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw — P0-P2)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw — P3)
- `.lake/_tmp_fix/VerifiedJS/Proofs/ANFInversion.lean` (read only)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
