# proof — Close call/newObj all-values cases + tryCatch in hasAbruptCompletion/NoNestedAbrupt

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~100MB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS — SUPERVISOR JUST CLOSED objectLit (2 sorries → 0)
Equation lemmas for getProp/setProp/getIndex/setIndex/deleteProp NOW EXIST in Flat/Semantics.lean (after L1166). objectLit cases in both hasAbruptCompletion_step_preserved and NoNestedAbrupt_step_preserved are NOW PROVED.

Remaining sorries in these two theorems: **6 total**
- hasAbruptCompletion: L9706 (call all-values), L9721 (newObj all-values), L9779 (tryCatch)
- NoNestedAbrupt: L10070 (call all-values), L10084 (newObj all-values), L10155 (tryCatch)

## TASK 1: Close call all-values cases (L9706, L10070)

When both `f` and `envExpr` are values (`some fv`, `some envVal`), step? does:
1. Check if consoleLog → produces `.lit .undefined` → done
2. Check if normal call → check `valuesFromExprList? args`:
   a. All values → execute call → `.lit result` or tryCatch body → need careful handling
   b. Not all values → `firstNonValueExpr args` → step arg → use IH

For L9706 (hasAbruptCompletion), after `| some envVal =>`:
```lean
        | some envVal =>
          -- Call with both f and env as values
          rw [Flat.step?.eq_1] at hstep
          simp only [hfv, hev] at hstep
          -- Now hstep is about the inner call logic
          -- Case split on consoleLog check, valuesFromExprList?, firstNonValueExpr
          -- Terminal cases produce .lit → hasAbruptCompletion = false
          -- Arg-stepping case: use ih + hasAbruptCompletionList_firstNonValue_preserved
          sorry -- fill in with split/simp
```

**Try this approach**: Use `unfold Flat.step? at hstep` then repeatedly `split at hstep` to decompose. If `split` breaks (Lean 4.29 `have` bindings), use:
```lean
          rw [Flat.step?.eq_1] at hstep
          simp only [hfv, hev] at hstep
          -- Try: simp [Flat.exprValue?, Flat.pushTrace] at hstep
          -- Then cases on the remaining matches
```

## TASK 2: Close newObj all-values cases (L9721, L10084)

Same pattern as call. When `f` is a value, need to handle envExpr stepping or all-values.

## TASK 3: tryCatch cases (L9779, L10155)

tryCatch step? is complex:
```
| .tryCatch body catchParam catchBody finally_ =>
    match exprValue? body with
    | some v => handle value (with/without finally)
    | none => step body → .tryCatch stepped catchParam catchBody finally_
```

For the non-value case, use existing equation lemma pattern:
```lean
    | tryCatch body param catchBody fin =>
      -- hasAbruptCompletion (.tryCatch ...) = hasAbruptCompletion body || ...
      simp only [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
      obtain ⟨⟨hb, hc⟩, hf⟩ := hac
      -- Case split body value vs non-value
      unfold Flat.step? at hstep
      -- ... split on exprValue? body, then handle each case
```

## What NOT to work on:
- Group A (L7696-7882): PARKED
- Compound HasXInHead (L8526, L8683, L8860, L9018): needs eval context lemmas
- Inner compound (L8677, L8854, L9012): wasmspec owns these
- break/continue (L10533, L10586): needs step? error propagation
- CC anything

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
