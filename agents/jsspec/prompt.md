# jsspec — CLOSE CC SORRIES: objectLit, arrayLit, tryCatch

## STATUS: ANF staging lemmas DELIVERED and INTEGRATED. CC is your domain now.

## CURRENT SORRY COUNT: ANF=17, CC=18, Wasm=19, Lower=1 → 55 total

## PRIORITY 0: objectLit (L2866), arrayLit (L2867) — EASY WINS

File: `VerifiedJS/Proofs/ClosureConvertCorrect.lean`

Use `lean_goal` at L2866 and L2867. These are likely stub implementations where closureConvert produces a simplified form. If the goal is straightforward (e.g., the converted form is identical or trivially related), close it.

Common pattern: if closureConvert just wraps/unwraps, the simulation is:
```lean
  | objectLit props =>
    -- Check: does closureConvert objectLit just produce objectLit with converted props?
    -- If so, use the stepping relation directly
    simp [Flat.closureConvert, Flat.convertExpr]
    sorry -- fill after seeing goal
```

## PRIORITY 1: tryCatch (L2958)

Use `lean_goal` at L2958. The tryCatch simulation follows the pattern:
- closureConvert preserves tryCatch structure
- Step the body, compose with catch handler
- May need the HeapInj invariant — if so, leave as sorry with a comment

## PRIORITY 2: setProp stepping case (L2648), setIndex stepping case (L2718)

These are cases where the sub-expression steps (not a value). Pattern:
```lean
  | setProp obj prop value =>
    -- If obj is not a value, it steps → closureConvert preserves the step
    -- Goal: show cc(setProp e p v) steps to cc(setProp e' p v) when e → e'
    sorry -- check with lean_goal
```

## PRIORITY 3: forIn/forOf with supported hypothesis (L1132, L1133)

Check if there's an `h_supported` or `supported` hypothesis in scope:
```lean
  | forIn => exfalso; simp [Flat.Expr.supported] at h_supported
  | forOf => exfalso; simp [Flat.Expr.supported] at h_supported
```

If no supported hypothesis is available at this point in the proof, SKIP.

## DO NOT edit: ANFConvertCorrect.lean, EmitCorrect.lean, EndToEnd.lean, LowerCorrect.lean
## YOU CAN edit: ClosureConvertCorrect.lean, .lake/_tmp_fix/**, VerifiedJS/Core/*, VerifiedJS/Flat/*
## Log to agents/jsspec/log.md
