# proof — CLOSE SECOND-POSITION HasReturnInHead CASES (L16490-L16501)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T15:30
- ANF: 45 real sorries. CC: 15 (jsspec). Total: 60.
- **step_error_isLit FULLY PROVED** — 0 sorries! tryCatch case closed by simp.
- **hasReturnInHead_return_steps**: seq_left, seq_right (Case A), call_func, newObj_func, and ALL first-position constructors FULLY PROVED.
- **12 second-position + list constructor sorries remain** at L16490-L16501 — THESE ARE YOUR TARGET
- **2 Case B sorries** at L16433, L16489 — defer, wasmspec will handle

## LINE NUMBERS SHIFTED — USE THESE UPDATED ONES:
- Second-position block: L16490-L16501 (was L16148-L16159)
- Case B sorries: L16433, L16489 (was L16091, L16147)
- await/yield compound: L16857, L17030

## DO NOT WORK ON:
- L16433, L16489 (Case B continuation — wasmspec owns)
- L10664-L11035 (trivialChain — LSP timeout zone)
- L17181-L17193 (while condition — blocked)
- L17918-L17958 (if_branch — blocked)
- L18799-L18820 (tryCatch — blocked)
- L20147-L20158 (noCallFrameReturn/body_sim — blocked)
- L16857, L17030 (await/yield compound — wasmspec owns)
- L17086-L17091 (return/yield .let compound — defer)

## P0: Second-position cases (L16490-L16494) — 5 sorries → 0

These follow THE EXACT SAME PATTERN as seq_left and the proven Case A at L16437-16487.
The ONLY differences:
1. Different wrapper function (e.g., `.binary op lhs_val ·` instead of `.seq · b`)
2. Different ctx/error lemma names
3. The first sub-expression is already a value, so VarFreeIn/NoNestedAbrupt project differently

### ALL ctx/error lemmas exist (find with lean_hover_info):
- `step?_binary_rhs_ctx` / `step?_binary_rhs_error`
- `step?_setProp_val_ctx` / `step?_setProp_val_error`
- `step?_getIndex_idx_ctx` / `step?_getIndex_idx_error`
- `step?_setIndex_idx_ctx` / `step?_setIndex_idx_error`
- `step?_setIndex_val_ctx` / `step?_setIndex_val_error`

### EXACT PROOF for binary_rhs (L16490):

```lean
    | binary_rhs h_a =>
      rename_i op lhs_val a
      simp only [ANF.normalizeExpr] at hnorm
      have ha_depth : a.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      -- Use normalizeExpr_return_none_or_k / normalizeExpr_return_some_or_k depending on arg
      sorry -- FILL: follow Case A pattern from seq_right (L16437-16487)
      -- Key substitutions:
      --   wrapper: (.binary op (.lit lhs_val) ·)
      --   ctx lemma: step?_binary_rhs_ctx
      --   error lemma: step?_binary_rhs_error
      --   VarFreeIn: VarFreeIn.binary_rhs
      --   NoNestedAbrupt: (by cases hna with | binary _ ha => exact ha)
```

### CRITICAL: Check the match structure
Use `lean_goal` at L16490 to see the EXACT goal. The `arg` variable determines which normalizeExpr_return lemma to use:
- `arg = none` → `normalizeExpr_return_none_or_k`
- `arg = some t` → `normalizeExpr_return_some_or_k`

Look at the seq_right Case A proof at L16437-16487 as your TEMPLATE. Copy it exactly, substituting:
- `.seq · b` → `.binary op (.lit lhs_val) ·`
- `step?_seq_ctx` → `step?_binary_rhs_ctx`
- `step?_seq_error` → `step?_binary_rhs_error`
- `VarFreeIn.seq_l` → `VarFreeIn.binary_rhs`
- `(by cases hna with | seq ha _ => exact ha)` → `(by cases hna with | binary _ ha => exact ha)`

### APPROACH: Do one case at a time
1. Use lean_goal at L16490. Read seq_right Case A (L16437-16487) as template.
2. Write binary_rhs. Verify with lean_diagnostic_messages.
3. Write setProp_val (L16491). Verify.
4. Continue for getIndex_idx, setIndex_idx, setIndex_val.

## P1: call_env, newObj_env (L16495, L16497) — 2 sorries → 0

Same pattern as call_func/newObj_func but for second-position:
- `step?_call_env_ctx` / `step?_call_env_error`
- `step?_newObj_env_ctx` / `step?_newObj_env_error`

## P2: List constructor cases (L16496, L16498-L16501) — 5 sorries
These need list-stepping infrastructure. Defer — assess after P0/P1.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — second-position HasReturnInHead cases" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
