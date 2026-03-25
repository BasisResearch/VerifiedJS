# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 26 (in Semantics.lean)

### LowerSimRel cases (12 sorries, L6204-L6281)
```
L6204  let          sorry — rhs code + localSet, needs LowerCodeCorr.let_inv
L6212  seq          sorry — aCode ++ [drop] ++ bCode, needs 1:N stepping
L6216  if           sorry — condCode ++ [if_ ...], needs trivial evaluation
L6219  while        sorry — loop semantics
L6222  throw        sorry — error event
L6225  tryCatch     sorry — try/catch frame
L6266  return(some) sorry — return value evaluation
L6269  call         sorry — function call semantics
L6272  getProp      sorry — property access
L6275  setProp      sorry — property assignment
L6278  log          sorry — console.log
L6281  assign       sorry — variable assignment
```

### EmitSimRel cases (8 sorries)
```
L7929  i64 load     sorry — needs EmitCodeCorr.load_i64
L7932  load (next)  sorry — load continuation
L7935  load (next2) sorry — load continuation
L8376  emit case    sorry
L8379  emit case    sorry
L8616  emit case    sorry
L8619  emit case    sorry
L8726  emit case    sorry
```

### Init (3+3 `by sorry`)
```
L257   init sorry
L8885  LowerSimRel.init by sorry
L8900  LowerSimRel.init by sorry
L8924  LowerSimRel.init by sorry
```

## Priority: LowerSimRel `let` case (L6204)

The `let` case is the most fundamental — once it works, `seq`, `if`, `while` follow similar patterns.

**Structure**: ANF does `let name rhs body`:
- ANF step evaluates `rhs` (a ComplexExpr), binds result to `name`, continues with `body`
- IR code is `rhsCode ++ [localSet idx] ++ bodyCode` (from `LowerCodeCorr.let_inv`)

**Approach**:
1. Invert `hrel.hcode` with `hexpr` to get `LowerCodeCorr.let_inv`
2. Show IR executes `rhsCode` (simulating rhs evaluation)
3. Show IR executes `localSet idx` (binding the result)
4. Show remaining IR code corresponds to `body` with updated locals

```lean
    | .«let» name rhs body =>
        have hc := hrel.hcode; rw [hexpr] at hc
        -- Invert: code = rhsCode ++ [.localSet idx] ++ bodyCode
        cases hc with
        | let_ idx rhsCode bodyCode hrhs hbody =>
          -- ANF step: evaluate rhs, bind result, continue with body
          -- IR: execute rhsCode (produces value on stack), then localSet idx
          sorry
```

Use `lean_goal` at L6204 to see the exact goal before editing.

## Priority: Init `by sorry` (L8885, L8900, L8924)

These are small: need to show the initial LowerSimRel fields hold. Check what field is `by sorry` — likely a well-formedness condition on the initial IR state.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
