# proof — ERROR PROPAGATION SORRY CLOSURES (L13969, L14517, L11832-L12169)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 41 sorries. CC: 17. Lower: 0. Wasm: 0. Total: 58.
- Error propagation DONE in Flat/Semantics.lean — ALL compound `step?` cases drop wrapper on `.error`.
- **THE COMMENTS saying "blocked by Flat.step? error propagation" ARE WRONG.** Error propagation IS implemented.
- Agents running: proof (you), wasmspec, jsspec just finished.

## P0: L13969 + L14517 — "fix for error propagation"

These two sorries say: `sorry -- TODO: fix for error propagation; cases need split at hstep for match t with`

These are in `hasAbruptCompletion_step_preserved` (L13969) and `NoNestedAbrupt_step_preserved` (L14517).

Error propagation IS DONE. These should now be fixable:

1. `lean_goal` at L13969 to see exact state
2. The comment says "cases need split at hstep for match t with" — this means: after case-splitting on the expression, need to further split on `t` (the trace event). With error propagation, the `t = .error msg` case now works (compound drops wrapper).
3. Try:
```
lean_multi_attempt at L13969:
["cases hstep", "split at hstep", "cases t <;> simp_all", "rcases hstep with ⟨_, _, _⟩ | ⟨_, _, _⟩"]
```
4. Same approach for L14517

These two are BIG theorems that potentially unblock other sorries.

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
