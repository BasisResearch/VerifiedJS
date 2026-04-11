# proof — CLOSE SECOND-POSITION HasReturnInHead CASES NOW

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T17:05
- ANF: 44 real sorries. CC: 12. Total: 56.
- **wasmspec CLOSED Case B** — those sorries are GONE.
- **step_error_isLit tryCatch case closed** — sorry migrated to Steps_steppable (L15166).
- **YOUR LAST RUN (15:00-16:50)**: You spent 110 min on step_error_isLit tryCatch refactor. Net 0 sorry change. That's infrastructure — fine. But NOW YOU MUST CLOSE SECOND-POSITION CASES.

## YOUR ONLY TARGET: L16690-L16694 (5 second-position sorries)

These have been assigned to you for 3 RUNS. You have not started. START NOW.

### LINE NUMBERS (verified from file at 17:05):
```
L16690: | binary_rhs h_a => sorry
L16691: | setProp_val h_a => sorry
L16692: | getIndex_idx h_a => sorry
L16693: | setIndex_idx h_a => sorry
L16694: | setIndex_val h_a => sorry
```

### THE TEMPLATE: Look at seq_right Case A (L16425-L16500)
The pattern for each second-position case with `some arg_t` is:

```lean
-- For binary_rhs h_a (L16690), the proof is:
-- 1. The match on `arg` (none/some) is already done above at L16422
-- 2. For each arg case, rcases normalizeExpr_return_*_or_k gives Case A / Case B
-- 3. Case A: IH on the sub-expression with HasReturnInHead
-- 4. Use Steps_compound_error_lift with the appropriate ctx/error lemmas
```

### ALL CTX/ERROR LEMMAS EXIST (verified):
- `step?_binary_rhs_ctx` (L1833) / `step?_binary_rhs_error` (L2518)
- `step?_setProp_val_ctx` (L1924) / `step?_setProp_val_error` (L2532)
- `step?_getIndex_idx_ctx` (L2018) / `step?_getIndex_idx_error` (L2546)
- `step?_setIndex_idx_ctx` (L2037) / `step?_setIndex_idx_error` (L2560)
- `step?_setIndex_val_ctx` (L1943) / `step?_setIndex_val_error` (L2574)

### CRITICAL: Read surrounding match context first
1. `lean_goal` at L16690 to see EXACT hypotheses and goal
2. Read L16412-L16500 (seq_right case) to understand the Case A/B split pattern
3. Each second-position case follows EXACTLY the same structure as the first-position cases

### APPROACH: One case at a time
1. Read L16690 context with lean_goal
2. Write binary_rhs proof (L16690). Verify with lean_diagnostic_messages
3. Write setProp_val (L16691). Verify.
4. Continue through all 5.

### WHAT YOU SUBSTITUTE per case:
| Case | Wrapper | ctx lemma | error lemma | VarFreeIn | NoNestedAbrupt |
|------|---------|-----------|-------------|-----------|----------------|
| binary_rhs | `(.binary op (.lit lhs_val) ·)` | step?_binary_rhs_ctx | step?_binary_rhs_error | VarFreeIn.binary_rhs | `by cases hna with \| binary _ ha => exact ha` |
| setProp_val | `(.setProp (.lit ov) prop ·)` | step?_setProp_val_ctx | step?_setProp_val_error | VarFreeIn.setProp_val | `by cases hna with \| setProp _ _ ha => exact ha` |
| getIndex_idx | `(.getIndex (.lit ov) ·)` | step?_getIndex_idx_ctx | step?_getIndex_idx_error | VarFreeIn.getIndex_idx | `by cases hna with \| getIndex _ ha => exact ha` |
| setIndex_idx | `(.setIndex (.lit ov) · val)` | step?_setIndex_idx_ctx | step?_setIndex_idx_error | VarFreeIn.setIndex_idx | `by cases hna with \| setIndex _ ha _ => exact ha` |
| setIndex_val | `(.setIndex (.lit ov) (.lit iv) ·)` | step?_setIndex_val_ctx | step?_setIndex_val_error | VarFreeIn.setIndex_val | `by cases hna with \| setIndex _ _ ha => exact ha` |

## AFTER P0: call_env, newObj_env (L16695, L16697) — same pattern
- `step?_call_env_ctx` (L1962) / `step?_call_env_error` (L2588)
- `step?_newObj_env_ctx` (L1999) / `step?_newObj_env_error` (L2602)

## DO NOT WORK ON:
- L10704-L11075 (trivialChain — LSP timeout zone)
- L17381-L17393 (while condition — blocked)
- L18118-L18158 (if_branch — blocked)
- L18999-L19020 (tryCatch — blocked)
- L20347-L20358 (noCallFrameReturn/body_sim — blocked)
- ClosureConvertCorrect.lean
- step_nonError_preserves_noTryCatchInHead (L15166) — defer

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — second-position cases L16690-L16694" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
