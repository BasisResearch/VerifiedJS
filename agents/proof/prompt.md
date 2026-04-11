# proof — UNCOMMENT TWO PROOFS (L13969, L14517)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 42 sorries. CC: 17. Lower: 0. Total: 59.
- Error propagation DONE in Flat/Semantics.lean.
- **NO PROGRESS SINCE LAST RUN.** You must close at least 2 sorries this run.

## P0: UNCOMMENT hasAbruptCompletion_step_preserved (L13969)

**THIS IS A 3-LINE EDIT. DO IT FIRST.**

The proof is ALREADY WRITTEN in a comment block L13970-L14507. You just need to:

1. Delete line 13969: `  sorry -- TODO: fix for error propagation; cases need split at hstep for match t with`
2. Delete line 13970: `  /-cases e with` → change to `  cases e with`
3. Delete the closing `-/` at line 14507

That's it. The 537-line proof between L13971 and L14506 is complete and handles all cases.

**After uncommenting**, run `lean_diagnostic_messages` on lines 13962-14507 to check for errors. If there are errors, they'll be minor (hypothesis name shifts). Fix them one by one.

## P1: UNCOMMENT NoNestedAbrupt_step_preserved (L14517)

Same pattern. The proof is commented out from L14518 to L15035.

1. Delete line 14517: `  sorry -- TODO: fix for error propagation; cases need split at hstep for match t with`
2. Delete line 14518: `  /-obtain ⟨e, env, heap, trace, funcs, cs⟩ := sf` → change to `  obtain ⟨e, env, heap, trace, funcs, cs⟩ := sf`
3. Delete the closing `-/` at line 15035

**These two uncomments potentially close 2 sorries immediately** and may cascade to help L15443/L15514 (compound Category B cases that use these theorems).

## P2: COMPOUND ERROR PROP SORRIES (L11832, L11838, L12005, L12011, L12163, L12169)

After P0+P1, tackle these. They're marked "blocked by Flat.step? error propagation" but error prop IS done:
- L11832/L11838: return compound
- L12005/L12011: await compound
- L12163/L12169: yield compound

Pattern: when inner expr steps with `.error msg`, the compound wrapper drops. Use:
1. `Steps_ctx_lift` for non-error prefix (hnoerr holds for silent steps)
2. `step?_return_error` / `step?_await_error` / `step?_yield_error` for the final error step

## SKIP: labeled_branch (blocked by trivial mismatch), CC, while/tryCatch, if_branch, anfConvert_step_star

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — uncomment L13969 L14517" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
