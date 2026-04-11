# proof — CLOSE L17283/L17354 (final two standalone sorries) + L16999 (noCallFrameReturn)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- hasAbruptCompletion_step_preserved: PROVED
- NoNestedAbrupt_step_preserved: PROVED
- ANF: 33 sorries. CC: 14 (jsspec). Total: 47.

## ⚠️ DO NOT WORK ON:
- L10183-L10554 (trivialChain — BLOCKED by ANF trivial ↔ flat value mismatch)
- L13351-L13407 (callStack condition sorries — wasmspec owns these)
- L13763/L13936/L13992-L13997 (HasAwait/HasYield — wasmspec owns)
- L14033-L14864 (while/if — BLOCKED)
- L15705-L15726 (tryCatch — BLOCKED)
- L12969 (compound cases — wasmspec)

## P0: L17283, L17354 — TWO STANDALONE SORRIES

These are in `normalizeExpr_step_sim` (the main simulation theorem). Run `lean_goal` at both to understand what they need.

1. Read context around L17283 and L17354 (±30 lines)
2. Run `lean_goal` at each position
3. Based on the goal, determine if they're closable or blocked
4. If closable, write the proof. Verify with `lean_diagnostic_messages`.

## P1: L16999 — noCallFrameReturn

The sorry needs `catchParam ≠ "__call_frame_return__"`.

**APPROACH**: The `catchParam` comes from the SOURCE program's tryCatch. normalizeExpr preserves the original catchParam. The string `"__call_frame_return__"` is an internal Flat mechanism name never used by source programs.

1. Check if there's a hypothesis about `catchParam` being from normalizeExpr
2. The key fact: normalizeExpr for `.tryCatch body catchParam catch_ fin` produces a flat tryCatch with the SAME `catchParam`. The source program's supported fragment would never use `"__call_frame_return__"` as a catch parameter name.
3. You may need to add a `Source.supported` condition that excludes this internal name, or prove it from existing wellformedness conditions.

If this requires architectural changes (new preconditions), document what's needed and move on.

## P2: Investigate L17010 (body_sim)

The comment says "needs anfConvert_step_star to be proved by strong induction". This is the big theorem. Don't try to close it, but check:
1. What does the goal look like?
2. What infrastructure would be needed?
3. Write a clear analysis in the log.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — L17283/L17354 + L16999" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
