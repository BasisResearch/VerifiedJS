# proof — ERROR PROPAGATION SORRY CLOSURES (L13969, L14517, L11832-L12169)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 42 sorries (+1 from your decomposition). CC: 17. Lower: 0. Wasm: 0. Total: 59.
- Error propagation DONE in Flat/Semantics.lean — ALL compound `step?` cases drop wrapper on `.error`.
- **THE COMMENTS saying "blocked by Flat.step? error propagation" ARE WRONG.** Error propagation IS implemented.
- Agents running: proof (you), wasmspec, jsspec just finished.

## P0: L13969 — UNCOMMENT THE PROOF (it's already written!)

**CRITICAL DISCOVERY**: The proof for `hasAbruptCompletion_step_preserved` is ALREADY WRITTEN in a comment block from L13970 to L14507. It handles ALL expression cases including tryCatch with/without finally. The error propagation splits (`split at hstep <;>`) are ALREADY PRESENT in the commented-out code.

**DO THIS:**
1. Delete the `sorry -- TODO...` at L13969
2. Delete the `/-` at L13970
3. Delete the `-/` at L14507
4. This UNCOMMENTS the full proof

The commented-out proof ALREADY handles error propagation correctly:
- For compound cases, it does `split at hstep` then `split at hstep <;>` which handles both `.error _` and non-error branches
- For tryCatch, it handles all the isCallFrame logic (L14454-14506)
- ALL base cases (var, this, lit, labeled, while) are covered

**If uncommented proof has errors:** They'll likely be minor (line-number shifts from earlier edits, or `by assumption` needing an explicit hypothesis). Fix them individually.

## P0b: L14517 — NoNestedAbrupt_step_preserved

Same approach: look for a commented-out proof below the sorry. If not present, follow the same pattern as the hasAbruptCompletion proof but for NoNestedAbrupt. This is structurally identical (case split on expression, compound cases recurse).

These two are BIG theorems that potentially unblock L15443 and L15514 (compound Cat B sorries).

## P1: COMPOUND "blocked by error propagation" SORRIES (6)

After P0, tackle these — they are ALL marked "blocked by error propagation" but error propagation IS done:
- L11832 — compound inner_val (return)
- L11838 — compound HasReturnInHead
- L12005 — compound inner_arg (await)
- L12011 — compound HasAwaitInHead
- L12163 — compound inner_val (yield)
- L12169 — compound HasYieldInHead

For each:
1. `lean_goal` to see the actual state
2. Error propagation means: when inner expr steps with `.error msg`, the compound wrapper drops
3. You need: `Steps_ctx_lift` for non-error prefix + `step?_*_error` for the final error step
4. `Steps_ctx_lift` requires `hnoerr` — decompose: lift non-error steps, then add final error step separately

Pattern for seq case (adapt for return/await/yield):
```lean
-- Steps from inner = [silent steps] ++ [error step]
-- Lift [silent steps] through context using Steps_ctx_lift (hnoerr holds for silent)
-- Final error step: use step?_return_error / step?_await_error / step?_yield_error
```

## P2: L11522 — compound catch-all

This is the big catch-all for compound cases in normalizeExpr_throw_step_sim.
29 compound constructors. Even decomposing into separate sorry per constructor is progress.

## SKIP: labeled_branch (wasmspec confirmed ALL blocked by trivial mismatch), CC (jsspec), while/tryCatch, if_branch, anfConvert_step_star

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — error prop sorries L13969 L14517" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
