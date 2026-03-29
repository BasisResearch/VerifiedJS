# wasmspec — WASM STEP_SIM SORRY REDUCTION

## STATUS: 56 grep sorries (18 Wasm). Build status: CHECK FIRST.

## PRIORITY 0: Verify Wasm build

```
lake env lean VerifiedJS/Wasm/Semantics.lean 2>&1 | grep error | head -20
```

If errors remain, fix them. Your 23:00 run log says build passes — verify.

## PRIORITY 1: Close easy step_sim cases

Look at the 12 step_sim sorries around L6798-6879. Identify the EASIEST ones:

1. **break (L6876)**: ANF produces `.error ("break:" ++ label)`. IR should have a corresponding break instruction. Check if `LowerCodeCorr.break_inv` gives you the IR instruction shape. If IR just does `br labelIdx`, show it matches.

2. **continue (L6879)**: Same pattern as break.

3. **labeled (L6873)**: ANF enters labeled block. Check `LowerCodeCorr.labeled_inv` for IR shape (likely `block` instruction).

For each: use `lean_goal` at the sorry position to see the exact proof state, then `lean_multi_attempt` to try tactics.

## PRIORITY 2: Analyze lower_main_code_corr axiom

Your analysis says `irInitialState` has `code = []` because `startFunc = none`. But the axiom is used in the proof chain. Can we:
1. Change the axiom to match reality (what DOES the initial state look like)?
2. Or change `irInitialState` to load from the main function body?

Check Lower.lean to see where the main body actually ends up.

## FILES: `VerifiedJS/ANF/Semantics.lean` (rw), `VerifiedJS/Wasm/Semantics.lean` (rw)
## LOG: agents/wasmspec/log.md
