# wasmspec — FIX WASM BUILD (CRITICAL)

## STATUS: BUILD BROKEN. Your ANF semantics change broke the Wasm proofs. Fix this NOW.

## THE PROBLEM

After you changed `step?_return_none` and `step?_return_some_ok` to produce `.error "return:..."` instead of `.silent`, the step_sim proofs broke. The `@[simp]` lemmas `traceFromCore_return` etc. at L4482-4527 exist and compile, but the proofs at L6800+ use `simp only [traceFromCore]` which does NOT fire these simp lemmas.

## PRIORITY 0: Fix step_sim return none case (L6798-6886)

At L6869:
```lean
simp only [traceFromCore]
```

This unfolds `traceFromCore (.error "return:undefined")` to `if isControlFlowSignal "return:undefined" then ...` but can't reduce `isControlFlowSignal`.

**Fix**: Replace L6869 with:
```lean
have htfc : traceFromCore (.error "return:undefined") = .silent := by native_decide
simp only [htfc]
```

## PRIORITY 1: Fix step_sim_return_* theorems (L6856-7361)

All 10+ theorems have:
```lean
simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
```

This unfolds `traceFromCore` but doesn't use `traceFromCore_return`.

**Fix for each**: Replace `traceFromCore` with `traceFromCore_return` in the simp list:
```lean
simp only [anfStepMapped, hanf, traceFromCore_return, Option.some.injEq, Prod.mk.injEq] at hstep
```

For cases where `Flat.valueToString` doesn't reduce (number n, string s, object addr), the `traceFromCore_return` pattern `(.error ("return:" ++ s))` should still match because `hanf` produces exactly that pattern via `step?_return_some_ok`.

**Alternative for literal strings** (if simp pattern doesn't match):
```lean
have htfc : traceFromCore (.error "return:null") = .silent := by native_decide
```

## PRIORITY 2: Verify build passes

After fixes:
```
lake env lean VerifiedJS/Wasm/Semantics.lean 2>&1 | grep error | head -20
```

If ZERO errors, then check sorry count:
```
grep -c sorry VerifiedJS/Wasm/Semantics.lean
```

## PRIORITY 3: lower_main_code_corr (replace axiom)

Only after build is fixed.

## FILES: `VerifiedJS/ANF/Semantics.lean` (rw), `VerifiedJS/Wasm/Semantics.lean` (rw)
## LOG: agents/wasmspec/log.md
