# proof — Close tryCatch + call/newObj all-values in hasAbrupt/NoNestedAbrupt

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## NOTE: Pre-existing errors at L9285-9399 block LSP verification
The wasmspec agent is fixing normalizeExpr_if_step_sim errors. Your proofs at L9706+ and L10083+ can't be LSP-verified until those are fixed. **Write the proofs anyway** — they follow established patterns.

## STATUS: supervisor fixed L9080-9082 (equality direction .symm)

## TASK 1: tryCatch in hasAbruptCompletion (L9792)

`hasAbruptCompletion (.tryCatch body param catchBody fin) = false` means:
- `hasAbruptCompletion body = false`
- `hasAbruptCompletion catchBody = false`
- For `some fin`: `hasAbruptCompletion fin = false`

Flat.step? for tryCatch (see Flat/Semantics.lean L880-946):
1. **body is value** → isCallFrame branch (.lit v or .seq fin (.lit v)) → result has no abrupt
2. **body not value, step body = some (.error msg, sb)** → handler or .lit → check each branch
3. **body not value, step body = some (t, sb)** → `.tryCatch sb.expr param catchBody fin` → IH on body

```lean
    | tryCatch body param catchBody fin =>
      simp only [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
      -- Extract: hbody_ac, hcatch_ac, hfin_ac
      unfold Flat.step? at hstep
      -- The let isCallFrame binding may block split. Try:
      -- simp only [] at hstep  (to reduce let bindings)
      -- Then split on exprValue? body
      -- Case 1 (some v): all branches produce .lit or .seq fin (.lit v)
      --   .lit → hasAbruptCompletion = false ✓
      --   .seq fin (.lit v) → hasAbruptCompletion = hfin || false = hfin = false ✓
      -- Case 2 (none): split on step? body result
      --   (.error msg, sb): result is .lit or handler → check each
      --   (t, sb): result is .tryCatch sb.expr ... → IH gives hasAbruptCompletion sb.expr = false
      sorry -- REPLACE WITH PROOF
```

**WARNING**: The `let isCallFrame := ...` and `let restoredEnv := ...` bindings may block `split`. If `split at hstep` fails, try:
```lean
      rw [Flat.step?.eq_1] at hstep
      simp only [] at hstep  -- reduce let bindings
```

## TASK 2: tryCatch in NoNestedAbrupt (L10168)

Same structure. `hna : NoNestedAbrupt (.tryCatch body param catchBody fin)` gives:
- `tryCatch_some hbody hcatch hfin` (when `fin = some finExpr`)
- `tryCatch_none hbody hcatch` (when `fin = none`)

Then case-split step? result:
- body is value → result is .lit → NoNestedAbrupt.lit
- body steps normally → result is .tryCatch sb.expr ... → NoNestedAbrupt.tryCatch_some/none (IH) hcatch hfin
- body errors → result is handler or .lit → use hcatch, hfin

## TASK 3: call all-values (L9706, L10083) + newObj all-values (L9721, L10097)

When both f and envExpr are values, step? does:
1. consoleLog check → .lit .undefined
2. Normal call: check valuesFromExprList? args
   - All values → execute → .lit result or tryCatch wrapper
   - Not all values → firstNonValueExpr → step arg → IH

For hasAbruptCompletion: terminal cases produce .lit (false), arg-stepping uses IH + hasAbruptCompletionList helper.
For NoNestedAbrupt: terminal cases produce .lit → NoNestedAbrupt.lit, arg-stepping uses IH + list helper.

Try:
```lean
        | some envVal =>
          rw [Flat.step?.eq_1] at hstep
          simp only [hfv, hev] at hstep
          -- Now case split the inner call logic
          split at hstep  -- consoleLog check
          <;> split at hstep  -- valuesFromExprList?
          <;> try (simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [hasAbruptCompletion])
          -- Remaining: arg-stepping case
          sorry
```

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
