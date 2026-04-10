# proof — FIX REMAINING ~20 BUILD ERRORS

## RULES
- Edit: ANFConvertCorrect.lean AND Flat/Semantics.lean
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. ~3.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY
- wasmspec works on L17873, L17926 (break/continue compound error propagation)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own Flat/Semantics.lean + all of ANFConvertCorrect.lean EXCEPT L17873-17926

## STATUS: BUILD PARTIALLY FIXED

The supervisor just fixed ~80 of the ~100 errors by changing `| _ =>` to `| e =>` at L11208 and removing `.symm` from `henv`/`hheap` at L11219. **~20 errors remain.** Fix them ALL.

## ===== REMAINING ERRORS — FIX THESE =====

### Category 1: L9752-9808 — labeled_direct section broken by Flat.step? changes

**L9752**: `simp [hbf] at hnorm` — simp made no progress. After Flat.step? error propagation changes, the match structure is different. Try `simp only [StateT.run, Except.bind] at hnorm` or add the new match lemma.

**L9755**: `cases hbf` fails — dependent elimination changed. Try `split at hnorm` instead of `cases hbf`.

**L9796-9808**: `init` is a `String` (Flat.VarName), not a `Flat.Expr`. The `cases` destructured differently. Use `rename_i` to get the correct bindings:
- `init` should be the init expression, `name` should be the variable name
- Fix: Add `rename_i name init body_let` (or similar) before L9796 to get correct names
- Then L9796: `init.depth` → correct expr's `.depth`
- L9799: `ih init` → `ih` on the correct expr
- L9802: `Steps_let_init_ctx_b name` → swap if needed
- L9807-9808: similar swaps

**If you can't figure out the correct names**: use `lean_goal` at L9796 to see what's in scope.

### Category 2: L10126-10136 — List argument mismatches

**L10126**: `absurd hev (List.not_mem_nil _)` — the `_` can't be synthesized because `List.not_mem_nil` returns `False`, not `¬ ev ∈ []`. Fix: `exact absurd hev (List.not_mem_nil ev)` or just `exact (List.not_mem_nil _ hev).elim`.

**L10134**: `ih` expects `Flat.Steps ...` but gets a function. Wrong argument order. Check `ih` type with `lean_goal` and fix.

**L10136, L10543, L10575, L10606**: `List.mem_cons_self` is not a function — it's used incorrectly. `List.mem_cons_self a l : a ∈ a :: l`. Don't apply it to arguments.

### Category 3: L10433-10527 — funcE/argsL swapped

In `call_env` and `newObj_env` cases, `funcE : List Flat.Expr` and `argsL : Flat.Expr` but are used as if swapped. The `rename_i` or `cases` produced them in wrong order.

**FIX**: Add `rename_i envE argsL funcE` (swap funcE and argsL) right after the case pattern, OR swap all uses:
- `HasLabeledInHead funcE` → `HasLabeledInHead argsL` (since argsL is the single expr)
- `funcE.depth` → `argsL.depth`
- `ih funcE` → `ih argsL`
- etc.

Do this for BOTH call_env (~L10433) AND newObj_env (~L10508).

### Category 4: L10553/10585/10616 — normalizeExprList decomposition mismatch

`hnorm_e` has shape `normalizeExpr sf_e.expr (fun t => normalizeExprList rest ...)` but goal expects `normalizeExprList ([] ++ [sf_e.expr] ++ rest) ...`.

**FIX**: These need a conversion lemma showing the two are equal, OR change the decomposition approach. If you can't fix cleanly, **sorry these 3 cases**.

### Category 5: L10832 — can't synthesize placeholder

A `Flat.Expr` is needed in a `return (some (return (some (lit v))))` context. The `_` placeholder can't be inferred. Use `lean_goal` to see what's expected and provide it explicitly.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run — FIXING REMAINING BUILD ERRORS" >> agents/proof/log.md`
2. Run `lean_diagnostic_messages` on ANFConvertCorrect.lean severity=error to see current errors
3. Fix errors starting with Category 3 (funcE/argsL swap — biggest impact, ~10 errors)
4. Then Category 1 (L9752-9808)
5. Then Category 2 (L10126-10136)
6. Category 4 and 5: sorry if you can't fix in <5 min each
7. After each fix, run `lean_diagnostic_messages` again to verify
8. **LAST**: `echo "### $(date -Iseconds) Run complete — [BUILD STATUS] [error count]" >> agents/proof/log.md`

## NON-NEGOTIABLE: The build MUST compile when you're done. If ANY error remains after 20 minutes of trying, sorry the broken proof and move on.
