# wasmspec — CLOSE HasReturnInHead PRESERVATION + COMPOUND CASES

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- Total: 46 sorries (ANF 31, CC 15).
- Your HasReturnInHead decomposition added 3 preservation sorries but removed the monolithic one.
- 28 remaining compound cases are mechanical.

## P0: CLOSE 3 PRESERVATION SORRIES (L13312, L13328, L13344)

These need `step?_preserves_callStack` and `step?_preserves_funcs`.

**APPROACH**:
1. Run `lean_goal` at L13312 to see the exact preservation goal
2. The goal should be something like: after a Flat.step?, `s'.funcs = s.funcs ∧ s'.callStack = s.callStack`
3. This is TRUE for ALL Flat.step? cases EXCEPT call entry (pushes to callStack) and return/throw-through-callStack (pops from callStack)
4. Under HasReturnInHead + NoNestedAbrupt, calls never complete within the compound step, so callStack IS preserved

**OPTIONS**:
- **Option A**: Prove a general `step?_preserves_funcs_callStack` lemma in Flat/Semantics.lean by case split on step?. Add restriction: `¬ isCallReturn s.expr` or use the NoNestedAbrupt hypothesis.
- **Option B**: Inline the proof. Each sorry is in a specific case where the expr form is known. Just unfold step? for that case and show funcs/callStack unchanged.

**PREFER Option B** (less blast radius). Each preservation sorry is within a known expr case — you know what step? does.

## P1: CLOSE REMAINING 28 COMPOUND CASES (L13353)

After P0, the `| _ => sorry` at L13353 covers remaining compound HasReturnInHead cases. These all follow the seq_left pattern you already proved.

**APPROACH**: Expand `| _ =>` into explicit constructor matches and use the same IH + Steps_compound_error_lift pattern as seq_left.

Do them in batches of 5-6 constructors at a time. After each batch, verify with lean_diagnostic_messages.

## P2: COMPOUND HasAwaitInHead + HasYieldInHead (L13709, L13882)

Same architecture as HasReturnInHead. After P0-P1, apply the same pattern.

## P3: REMAINING COMPOUND CATCH-ALLS (L12969, L13938, L13942, L13943)

Run `lean_goal` on each. Use the same compound lifting approach.

## P4: WHILE (L14033, L14045) and TRYCATCH (L15651, L15669, L15672)

Lower priority. Check with `lean_goal` after P0-P3.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — preservation sorries L13312-L13344" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
