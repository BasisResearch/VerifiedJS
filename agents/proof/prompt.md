# proof — RESTORE hasAbruptCompletion/NoNestedAbrupt + COMPOUND ERROR CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- BUILD PASSES. 0 errors.
- ANF: 48 sorries. CC: 15. Lower: 0.
- Error propagation DONE in Flat/Semantics.lean.
- Your last 2 runs exited code 1 before doing work. If something crashes you, TRY SMALLER EDITS.

## IMPORTANT: SKIP CALLSTACK WEAKENING
The 4 sorries at L2983, L3004, L3025, L3046 are in theorems (`Steps_throw_pres`, `Steps_return_some_pres`, `Steps_await_pres`, `Steps_yield_some_pres`) that have **ZERO callers**. They are dead code. Do NOT spend time on them.

## P0: RESTORE hasAbruptCompletion_step_preserved (L14072) — 1 SORRY

This theorem at L14065-14072 has a commented-out proof (L14073-L14610) that worked before error propagation changes. The proof needs updating because Flat.step? now has an extra `match` arm for error events.

Fix approach:
1. Uncomment the old proof (L14073-L14610)
2. For each `unfold Flat.step? at hstep` that now fails, add after it:
   ```lean
   split at hstep  -- splits on error vs non-error event
   · -- error case: s'.expr is inner expression result
     -- hasAbruptCompletion sf'.expr: need to show inner result has no abrupt
     sorry  -- we'll fix these individually
   · -- non-error case: original proof continues
     <original tactics>
   ```
3. Use `lean_multi_attempt` on the error case — often `simp [hasAbruptCompletion] at *` or the IH applies.

Even if you end up with 5-10 sorry'd error sub-cases, that's better than 1 monolithic sorry blocking everything.

## P1: RESTORE NoNestedAbrupt_step_preserved (L14620) — 1 SORRY

Same pattern as P0. Commented-out proof at L14621+. Same fix: uncomment, add error-case splits.

## P2: COMPOUND ERROR CASES (L11935, L11941, L12112, L12118, L12270, L12276) — 6 SORRIES

These say "blocked by Flat.step? error propagation" but error propagation IS DONE in Flat/Semantics.lean now. Check if they're now closable:
1. `lean_goal` at each location
2. The error propagation means compound expressions (seq, let, assign) now have defined step behavior when inner expr produces error
3. Try `lean_multi_attempt` with `["unfold Flat.step?; simp_all", "simp [Flat.step?]; split <;> simp_all"]`
4. If still blocked, document the EXACT missing piece

## CONCURRENCY
- wasmspec works on labeled_branch (L10333-L10706)
- jsspec works on ClosureConvertCorrect.lean only
- YOU own everything else in ANFConvertCorrect.lean

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — hasAbruptCompletion + NoNestedAbrupt restore" >> agents/proof/log.md`
2. P0: Uncomment and fix hasAbruptCompletion_step_preserved
3. P1: Uncomment and fix NoNestedAbrupt_step_preserved
4. P2: Check compound error cases
5. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
