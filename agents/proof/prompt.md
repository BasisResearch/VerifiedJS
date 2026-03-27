# proof — CLOSE 20 SORRY TOKENS IN 60 SECONDS (then 15 more)

## CONGRATULATIONS: Phase 3 is DONE (5/6 CCState stepping cases closed)
You already proved: let (L1989), if (L2208), seq (L2304), binary (L2550), getIndex (L2680).
Only while_ (L2957) remains from Phase 3.

## STEP 1 (DO FIRST — ONE sed COMMAND): 20 sorry tokens gone instantly

The old Phase 1 line numbers shifted. Use `grep -n` to find them, then sed:

```bash
sed -i "s/exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, sorry, sorry⟩/exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, hAgreeOut⟩/g" VerifiedJS/Proofs/ClosureConvertCorrect.lean
```

This hits exactly 10 lines (currently L2078, L2393, L2490, L2615, L2744, L2833, L2925, L3129, L3267, L3354).
Each has `hAgreeIn` and `hAgreeOut` in scope from the IH obtain on preceding lines.

**DO NOT BUILD YET** — do Step 2 first to batch fixes.

## STEP 2: Fix value-base CCStateAgree sorries (single `sorry` after `⟨rfl, rfl⟩`)

These lines have `⟨rfl, rfl⟩, sorry⟩`. The sorry needs CCStateAgree which is trivial for value expressions.

**Try this for each**: replace `sorry⟩` with `⟨rfl, rfl⟩⟩`

Current lines (use lean_goal to verify if unsure):
- L1825, L1848, L1876, L1899 (var/this value): `sorry⟩` → `⟨rfl, rfl⟩⟩`
- L2026, L2867 (assign/throw value): `sorry⟩` → `by simp [Flat.convertExpr]; exact ⟨rfl, rfl⟩⟩`
- L2115, L2245 (if-value true/seq-value): use lean_goal, try `⟨rfl, rfl⟩⟩` or `by simp [CCStateAgree, Flat.convertExpr]`
- L2137 (if-value false): `sorry, sorry⟩` — try `⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩`
- L2339 (unary value): same as L2115
- L2779 (deleteProp value): same pattern
- L2994, L3017, L3043, L3073 (while/break/continue/return): same pattern
- L3155, L3181, L3211, L3298 (yield/await/labeled): same pattern

Use `lean_multi_attempt` on a few to confirm which tactic works.

**NOW BUILD**: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## STEP 3: while_ CCState (L2957) — last Phase 3 case

Follow the exact pattern you used for let/if/seq/binary/getIndex:
```lean
-- while_ unrolls to: if cond (seq body (while_ cond body)) (lit undefined)
-- Need: convertExpr_state_determined chained for cond, body, cond-again, body-again
have hcond := convertExpr_state_determined cond scope envVar envMap st st_a <agree...>
-- Then chain through the compound expression
```
Use lean_goal at L2957 to see the exact goal shape.

## STEP 4: Hard cases (only after Steps 1-3 land)

Remaining after Steps 1-3:
- L2556/2557: call/newObj (jsspec has patches in .lake/_tmp_fix/)
- L2563/2622/2692: value sub-cases (heap reasoning)
- L2616/2686: setProp/setIndex full cases
- L2834/2835/2836: objectLit/arrayLit/functionDef
- L2926: tryCatch
- L1132/1133: forIn/forOf (skip — stubs)
- L1797: main suffices (skip)

## DO NOT TOUCH: ANFConvertCorrect, LowerCorrect, Wasm/Semantics

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log progress to agents/proof/log.md.
