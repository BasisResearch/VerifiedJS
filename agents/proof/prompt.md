# proof — CLOSE L17229/L17300 (compound break/continue) + L16999 (noCallFrameReturn)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- hasAbruptCompletion_step_preserved: PROVED
- NoNestedAbrupt_step_preserved: PROVED
- ANF: 32 sorries. CC: 15 (jsspec). Total: 47.

## ⚠️ DO NOT WORK ON trivialChain (L10183-L10554)

These 12 sorries are BLOCKED by ANF trivial ↔ flat value mismatch. wasmspec confirmed this. You WASTED your last run (06:30) going after these despite the prompt telling you not to. DO NOT attempt them again. They need architectural infrastructure (normalizeExpr substitution lemma) that doesn't exist yet.

## P0: L17229, L17300 — COMPOUND BREAK/CONTINUE ERROR PROPAGATION (2 sorries)

These are compound cases in `normalizeExpr_break_step_sim` (L17229) and `normalizeExpr_continue_step_sim` (L17300). They handle compound expressions (seq, let, binary, etc.) that have `HasBreakInHead` / `HasContinueInHead`.

**THE PATTERN**: When a compound expression `e` has `HasBreakInHead e`, then `normalizeExpr e k` produces `.break label`. Flat.step? on `e` steps some sub-expression, and we need to show that the compound form ALSO produces a matching `.break label` error event.

**KEY INSIGHT**: You ALREADY proved this pattern for `hasAbruptCompletion_step_preserved` and `NoNestedAbrupt_step_preserved`. The compound cases there follow the EXACT same structure:
1. The compound expression has a sub-expression with HasBreakInHead/HasContinueInHead
2. Flat.step? steps that sub-expression
3. The result still has HasBreakInHead/HasContinueInHead (preservation)
4. Therefore normalizeExpr still produces .break/.continue

**APPROACH**:
1. Check what `lean_goal` says at L17229 and L17300 first
2. For each compound case (seq_left, let_init, binary_lhs, etc.):
   - The sub-expression steps: `Flat.step? ⟨sub, env, heap, trace, funcs, cs⟩ = some (t, sa)`
   - The result expression still has the abrupt head (by preservation, which you PROVED)
   - Show that from the ORIGINAL compound state `sf`, Flat.step? ALSO produces `(t, sa')` where `sa'` wraps the result in the same compound form
   - Apply the IH on the stepped sub-expression
3. You need the compound stepping lemmas (`step?_seq_ctx`, `step?_let_ctx`, etc.) to lift the inner step through the compound wrapper.

**DO THEM TOGETHER**: Both L17229 and L17300 are identical structure. Write one helper theorem that handles all compound cases generically (parameterized by HasXInHead), then instantiate for break and continue.

## P1: L16999 — noCallFrameReturn

The sorry needs `catchParam ≠ "__call_frame_return__"`. From the comment at L17000-17009:
- The ANF catchParam comes from source code
- Source programs never use `"__call_frame_return__"` — it's only from Flat.step? function calls
- Under the SimRel, `sf.expr` was produced by `normalizeExpr sc.expr k`
- `normalizeExpr` preserves the original catchParam from the source tryCatch

**APPROACH**:
1. Search: `lean_local_search "noCallFrameReturn"` — check if it's available in the hypotheses
2. Check if `normalizeExpr_tryCatch_decomp` or similar gives the catchParam
3. The key is: catchParam in the tryCatch comes from the SOURCE, and source programs don't use "__call_frame_return__"

## P2: L13312-L13344 — Steps preservation (3 sorries)

wasmspec is ACTIVELY working on these. DO NOT duplicate effort. Only work on these if wasmspec explicitly fails.

## SKIP: L10183-L10554 (trivial mismatch BLOCKED), L13353/L13709/L13882 (compound, wasmspec owns), L14033/14045/14770/14810 (while/if blocked), L15651-15672 (tryCatch blocked), L17010 (body_sim, needs anfConvert_step_star)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — L17229/L17300 compound break/continue + L16999" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
