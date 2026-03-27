# proof — CC REMAINING + ANF DECOMPOSITION

## STATUS: 58 total sorries (was 99 — you closed 41! EXCELLENT WORK)

CC is down to 17 sorry tokens. ANF still has 13 sorries UNTOUCHED FOR 5+ DAYS. The end-to-end theorem CANNOT compose without anfConvert_step_star. You MUST pivot to ANF after finishing the CC mechanical leftovers.

## STEP 1: CC L2138 sorry,sorry (last mechanical pair)

At L2138, there is:
```lean
simp [sc', Flat.convertExpr], sorry, sorry⟩
```
This is the if-cond stepping case. The two sorries need CCStateAgree for `then_` and `else_` branch states after `convertExpr cond`. Use `lean_goal` at L2138 to see what's needed. Try:
```lean
lean_multi_attempt at L2138: ["hAgreeIn, hAgreeOut", "by exact CCStateAgree_refl _", "by simp [CCStateAgree]"]
```

## STEP 2: while_ CCState (L2958) — last Phase 3 case

Use your successful pattern from let/if/seq. Chain `convertExpr_state_determined` calls. Use `lean_goal` at L2958.

## STEP 3: PIVOT TO ANF (THIS IS CRITICAL)

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

The 13 sorries are already decomposed by constructor (L138-174). Each needs a proof. The architecture comment at L175-210 explains the approach.

**Start with the easiest cases:**

1. **break (L172), continue (L174)**: Produce error events directly. Should be straightforward — both ANF and Flat produce same event.
```lean
-- Try at L172:
simp_all [ANF.step?, Flat.step?]
-- or construct the witness explicitly
```

2. **throw (L155)**: Evaluate trivial arg, produce error event. Similar to break/continue.

3. **return (L159), yield (L161), await (L163)**: Evaluate optional trivial arg.

4. **var lookup (L138)**: step? resolves the variable in env. Match to Flat var lookup.

5. **seq (L149)**: Two sub-cases — a is value (skip to b) or step inner a.

6. **if (L151)**: Evaluate cond trivial, branch.

7. **let (L147)**: evalComplex evaluates rhs, extends env, continues.

8. **while (L153)**: Evaluate cond, unroll or terminate. Hardest.

9. **tryCatch (L157)**: Error handling cases. Hard.

10. **labeled (L170)**: Architecture issue noted — needs restructuring.

**Use `lean_goal` at each sorry, then `lean_multi_attempt` aggressively.**

Even replacing 1 monolithic sorry with 5 smaller ones is progress. The key is decomposing into sub-goals that can be attacked independently.

## STEP 4: Remaining CC hard cases (ONLY if ANF is progressing)

- call (L2557): jsspec staged helpers in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_call_patches.lean`
- Others (newObj, setProp, setIndex, objectLit, arrayLit, functionDef, tryCatch): design issues, lower priority

## DO NOT TOUCH: Wasm/Semantics.lean, LowerCorrect.lean

## Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
## Log progress to agents/proof/log.md.
