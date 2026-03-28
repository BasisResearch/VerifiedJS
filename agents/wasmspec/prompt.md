# wasmspec — ANF SEMANTICS FIX + LOWER_MAIN_CODE_CORR

## STATUS: 18 grep / 16 actual Wasm sorries. ALL step_sim 1:1 cases blocked (compound/1:N). Build passes.

## CRITICAL: You've failed to make the ANF semantics fix for 3+ runs. DO IT NOW.

## PRIORITY 0: Fix ANF break/continue/return/throw semantics

**File: `VerifiedJS/ANF/Semantics.lean`**

The ANF semantics produce `.silent` for break/continue/return but Core/Flat produce `.error`. This mismatch blocks ANF proofs. Fix these 4 cases:

### Fix 1: break (L447-449)
```lean
  | .«break» label =>
      let l := match label with | some s => "break:" ++ s | none => "break:"
      let s' := pushTrace { s with expr := .trivial .litUndefined } (.error l)
      some (.error l, s')
```

### Fix 2: continue (L450-452)
```lean
  | .«continue» label =>
      let l := match label with | some s => "continue:" ++ s | none => "continue:"
      let s' := pushTrace { s with expr := .trivial .litUndefined } (.error l)
      some (.error l, s')
```

### Fix 3: return none (L411-413)
```lean
      | none =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error "return:undefined")
          some (.error "return:undefined", s')
```

### Fix 4: return some — ok case (L415-418)
```lean
      | some t =>
          match evalTrivial s.env t with
          | .ok v =>
              let msg := "return:" ++ Core.valueToString v
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } (.error msg)
              some (.error msg, s')
```

### Fix 5: throw — ok case (L378-380)
```lean
      | .ok v =>
          let msg := Core.valueToString v
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
          some (.error msg, s')
```

`Core.valueToString` is in scope (file imports `VerifiedJS.Core.Semantics`).

### AFTER changing step?, fix the simp lemmas (L567-621):

1. `step?_break` (L567): change `.silent` to `.error l` with the match expression
2. `step?_continue` (L575): same
3. `step?_throw_ok` (L583): change `(.error "throw")` to `(.error (Core.valueToString v))`
   — add hypothesis `(v : Flat.Value)` and use it
4. `step?_return_none` (L601): change `.silent` to `(.error "return:undefined")`
5. `step?_return_some_ok` (L608): change `.silent` to `(.error ("return:" ++ Core.valueToString v))`

Each simp lemma proof is `simp [step?, h]` — should still work after the change.

**WARNING**: This WILL break 9 uses of `step?_return_some_ok` in step_sim_stutter (L6856-7341). Each one currently matches `.silent` and will need to match `.error "return:..."`. The proofs use `hanf` to derive the trace event, so updating the lemma statement should cascade correctly through `simp`. But CHECK:
```
lake env lean VerifiedJS/Wasm/Semantics.lean 2>&1 | grep "error" | head -20
```

If Wasm breaks, look at each `step?_return_some_ok` use site and update the proof to handle `.error` instead of `.silent`.

## PRIORITY 1: Prove lower_main_code_corr (replace axiom with theorem)

`lower_main_code_corr` at L6565 is an **axiom**. It should be a theorem proved from the `lower` function definition. This blocks the end-to-end proof at a fundamental level.

Check `VerifiedJS/Wasm/Lower.lean` for the `lower` and `lowerExpr` definitions. The theorem needs:
```lean
theorem lower_main_code_corr (prog : ANF.Program) (irmod : IRModule)
    (h : Wasm.lower prog = .ok irmod) :
    LowerCodeCorr prog.main (irInitialState irmod).code
```

If `lowerExpr` is private, you may need to make it `protected` or add a public wrapper.

## DO NOT ATTEMPT
- step_sim 1:1 cases (ALL blocked — compound/1:N)
- callIndirect (NOT exfalso, needs full proof)
- call cases (blocked by hframes_one)

## FILE: `VerifiedJS/ANF/Semantics.lean` (rw), `VerifiedJS/Wasm/Semantics.lean` (rw)

## WORKFLOW
1. Make ALL 5 step? definition changes at once
2. Update ALL 5 simp lemma statements
3. Build ANF/Semantics.lean first
4. Then build Wasm/Semantics.lean — fix any cascade errors
5. Build ANFConvertCorrect.lean — should still pass (sorries don't reference specific events)
6. Log to agents/wasmspec/log.md with EXACT sorry counts and build status
