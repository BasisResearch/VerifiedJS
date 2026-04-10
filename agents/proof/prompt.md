# proof — FIX THE BUILD. IT IS BROKEN.

## RULES
- Edit: ANFConvertCorrect.lean AND Flat/Semantics.lean
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. ~3.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY
- wasmspec works on L12288-12318 (return/yield/structural) and L16418-16439 (tryCatch)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own Flat/Semantics.lean + all of ANFConvertCorrect.lean

## STATUS: BUILD IS BROKEN. YOU BROKE IT IN YOUR 16:30 RUN. FIX IT NOW.

## ===== P0: FIX ALL ERRORS — DO THIS FIRST =====

Flat/Semantics.lean is clean — your error propagation changes for let/assign/seq landed correctly. Good.

But ANFConvertCorrect.lean has ~100 errors. Here are the categories:

### Error 1: L11211 — `Unknown identifier e` (repeated ~20 times)

At L11209-11211:
```lean
    | _ =>
      -- compound expression: use normalizeExpr_labeled_or_k + normalizeExpr_labeled_branch_step
      rcases ANF.normalizeExpr_labeled_or_k e k label body n m hnorm with hlh | ...
```

`e` is NOT in scope in this `| _ =>` catch-all. All other uses of `normalizeExpr_labeled_or_k` nearby (L10828, L10898, L10944, L11054, L11122, L11168) use `_` instead of `e`.

**FIX**: Either:
- Add `rename_i e` before L11211, OR
- Replace `e` with `_` at L11211 AND L11218

### Error 2: L11220 — Wrong Eq.symm direction

```lean
refine ⟨evs, sf', hsteps, ⟨k, n', m', hnorm', hk⟩, henv.symm, hheap.symm, ?_, h_obs_nil, hewf'⟩
```

`henv` and `hheap` from `normalizeExpr_labeled_branch_step` already have direction `sf_env = sf'.env`. The goal needs `sf'.env = sf_env`. So you need `henv.symm` only if henv has direction `sf'.env = sf_env`. Check the actual direction with `lean_goal` and fix accordingly. Compare with L11184 which uses `(hwenv.trans henv).symm` — no ctx lifting at L11220.

### Error 3: L9752 — `simp made no progress` in labeled_direct

```lean
cases hbf : (ANF.normalizeExpr body_flat K).run n with
| error msg => simp [hbf] at hnorm
```

After Flat.step? changes, `simp` unfolds differently. The fix likely needs to adapt the `simp` lemma set. Try `lean_diagnostic_messages` at this line and adjust.

### Error 4: L9796 — `init.depth` on String

```lean
have hinit_depth : init.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
```

`init` here is a `Flat.VarName` (String), not a `Flat.Expr`. Check what name the actual init expression has (it may be `init✝` or need a `rename_i`).

### Error 5: L10126 — `List.not_mem_nil` argument mismatch

```lean
| nil => intro ev hev; exact absurd hev (List.not_mem_nil _)
```

The `_` placeholder can't be synthesized. Try `List.not_mem_nil ev` instead.

### Error 6: L10134 — `List.mem_cons_of_mem` wrong usage

```lean
· exact ih (fun ev hev msg => hne ev (List.mem_cons_of_mem _ hev) msg) hobs ev hev
```

`ih` expects a `Flat.Steps` argument but gets a function. Check the `ih` type and fix the arguments.

### Error 7: L10433-10527 — funcE/argsL type swaps in call_env/newObj_env

```lean
HasLabeledInHead funcE  -- but funcE : List Flat.Expr, not Flat.Expr
```

Variables `funcE` and `argsL` are swapped. `funcE : List Flat.Expr` and `argsL : Flat.Expr`. Use `rename_i` to rebind or swap references.

### Error 8: L10553/10585/10616 — normalizeExprList/Props decomposition type mismatch

The `hnorm_e` has a different shape than expected. The `[] ++ [sf_e.expr] ++ rest` form doesn't match the direct form.

### Error 9: L4311 — `normalizeExpr_tryCatch_decomp` doesn't exist

Either define this lemma or sorry it and mark it as TODO.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run — FIXING BUILD" >> agents/proof/log.md`
2. Run `lean_diagnostic_messages` on ANFConvertCorrect.lean, severity=error
3. Fix errors ONE AT A TIME starting with L11211 (biggest impact — fixes ~80 of the ~100 errors)
4. After each fix, run `lean_diagnostic_messages` again to verify
5. If you can't fix an error cleanly, SORRY IT — a building sorry is better than a broken theorem
6. **LAST**: `echo "### $(date -Iseconds) Run complete — [BUILD STATUS]" >> agents/proof/log.md`

## NON-NEGOTIABLE: The build MUST pass when you're done. If ANY error remains, sorry the broken proof and move on.
