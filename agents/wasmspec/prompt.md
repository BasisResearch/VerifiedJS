# wasmspec — CLOSE 4 NoNestedAbrupt CONTRADICTION CASES

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY at break/continue sorries (~L15333-15400)

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- Supervisor collapsed if_branch, file now 16,269 lines (was 18,694)
- Proof agent is extending error propagation to ALL compound cases in Flat.step?
- ANF sorries: 39. CC: 15. Total: 54.

## P0: CLOSE 4 CONTRADICTION CASES IN BREAK/CONTINUE

Your earlier analysis found 4 of 32 cases are closable via NoNestedAbrupt contradiction:
- throw_arg, return_some_arg, yield_some_arg, await_arg

For these: `HasBreakInHead` (or `HasContinueInHead`) implies `hasAbruptCompletion arg = true`, but `NoNestedAbrupt` requires `hasAbruptCompletion arg = false`. This is a direct contradiction.

### Approach:
1. Find the break compound sorry (was L17758, now shifted ~-2400 lines → around L15360)
2. Find the continue compound sorry (was L17812, now shifted → around L15414)
3. For each, find the 4 contradiction cases (throw_arg, return_some_arg, yield_some_arg, await_arg)
4. Close them with:

```lean
| .throw_arg _ hb =>
  -- HasBreakInHead implies hasAbruptCompletion = true
  -- But NoNestedAbrupt requires hasAbruptCompletion = false
  -- Contradiction
  have : hasAbruptCompletion arg = true := HasBreakInHead_hasAbruptCompletion hb
  simp [this] at hnoabrupt  -- or exact absurd this hnoabrupt
```

### Helper lemma needed:
```lean
theorem HasBreakInHead_hasAbruptCompletion {e : Flat.Expr} (h : HasBreakInHead e) :
    hasAbruptCompletion e = true
```

This requires mutual induction on `HasBreakInHead` constructors. Check if it already exists with `lean_local_search` for "HasBreakInHead" and "hasAbruptCompletion".

If it doesn't exist, write it in ANFConvertCorrect.lean near the other HasBreakInHead lemmas.

## P1: PREPARE FOR REMAINING 28 CASES (DO NOT EDIT YET)

The other 28 cases need error propagation in Flat.step? (proof agent is adding it). Once done:
- Error from sub-expression → wrapper is stripped → `sa.expr` is directly the sub-result
- SimRel holds because no dead code wrapper
- Proof pattern: `have herr := step?_compound_error ...; rw [herr] at hstep; ...`

Prepare the proof outline for these cases but DO NOT edit until the proof agent confirms error propagation is in.

## P2: tryCatch sorries (L14018, L14036, L14039 after shift)

If P0 is done, analyze tryCatch compound sorries. These have different blockers (callStack + counter alignment).

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — NoNestedAbrupt contradiction cases" >> agents/wasmspec/log.md`
2. Find break/continue sorry positions in the CURRENT file (use grep for "sorry" near "break compound" or "continue compound")
3. Search for HasBreakInHead_hasAbruptCompletion helper
4. If missing, write it
5. Close the 4 contradiction cases
6. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
