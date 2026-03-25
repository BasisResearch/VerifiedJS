# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 24 (in Semantics.lean) + 1 misc (L262)

### LowerSimRel cases (12 sorries, L6205-L6286)
```
L6209  let          sorry — rhs code + localSet
L6217  seq          sorry — aCode ++ [drop] ++ bCode, needs 1:N stepping
L6221  if           sorry — condCode ++ [if_ ...]
L6224  while        sorry — loop semantics
L6227  throw        sorry — error event
L6230  tryCatch     sorry — try/catch frame
L6271  return(some) sorry — return value evaluation
L6274  call         sorry — function call semantics
L6277  getProp      sorry — property access
L6280  setProp      sorry — property assignment
L6283  log          sorry — console.log
L6286  assign       sorry — variable assignment
```

### EmitSimRel cases (8 sorries)
```
L7928  i64 load     sorry — needs EmitCodeCorr.load_i64
L7931  load (next)  sorry
L7934  load (next2) sorry
L8375  emit case    sorry
L8378  emit case    sorry
L8615  emit case    sorry
L8618  emit case    sorry
L8725  emit case    sorry
```

### Init (4 `by sorry`)
```
L262   init sorry
L8884  LowerSimRel.init by sorry
L8899  LowerSimRel.init by sorry
L8923  LowerSimRel.init by sorry
```

## Priority: LowerSimRel `let` case (L6209)

The `let` case is the most fundamental — once it works, `seq`, `if`, `assign` follow similar patterns.

**Structure**: ANF does `let name rhs body`:
- ANF step evaluates `rhs`, binds result to `name`, continues with `body`
- IR code is `rhsCode ++ [localSet idx] ++ bodyCode` (from `LowerCodeCorr.let_inv`)

**Approach**:
1. Use `lean_goal` at L6209 to see the exact goal
2. Invert `hrel.hcode` with `hexpr` to get `LowerCodeCorr.let_inv`
3. Show IR executes `rhsCode` → `localSet idx` → `bodyCode`

```lean
    | .«let» name rhs body =>
        have hc := hrel.hcode; rw [hexpr] at hc
        cases hc with
        | let_ idx rhsCode bodyCode hrhs hbody =>
          sorry
```

## Priority: Init `by sorry` (L8884, L8899, L8923)

These are small: need to show the initial LowerSimRel fields hold. Use `lean_goal` at each line to see what field needs proving.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
