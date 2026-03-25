# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 24 (in Semantics.lean)

### LowerSimRel.step_sim cases (12 sorries, L6205-L6286)
```
L6209  let          sorry — rhsCode ++ [localSet idx] ++ bodyCode
L6217  seq          sorry — aCode ++ [drop] ++ bCode, 1:N stepping
L6221  if           sorry — condCode ++ [if_ ...]
L6224  while        sorry — loop semantics
L6227  throw        sorry — error event
L6230  tryCatch     sorry — try/catch frame
L6271  return(some) sorry — return value evaluation
L6274  yield        sorry
L6277  await        sorry
L6280  labeled      sorry
L6283  break        sorry
L6286  continue     sorry
```

### EmitSimRel cases (7 sorries)
```
L7928  i64 load     sorry — needs EmitCodeCorr.load_i64
L7935  store        sorry
L7938  store8       sorry
L8379  emit case    sorry
L8382  emit case    sorry
L8619  emit case    sorry
L8622  emit case    sorry
L8729  emit case    sorry
```

### Init + misc (5 `by sorry`)
```
L262   readLE?      sorry — provable (see below)
L8888  LowerSimRel.init by sorry — needs LowerCodeCorr for init program
L8903  LowerSimRel.init by sorry — same
L8927  LowerSimRel.init by sorry — same
```

## Priority 1: readLE? (L262) — QUICK WIN

Goal: `readLE? mem addr width = none` given `mem.size = 0` and `¬addr + 0 < mem.size`.

The loop `for k in [0:width]` at k=0 checks `addr + 0 < mem.size`, which is false (from hbound). So it returns `none` immediately. Try:
```lean
-- Unfold readLE? and show the first iteration fails the bounds check
simp [readLE?]
-- If simp doesn't work, try induction on width or unfold the forIn for Std.Range
```
Use `lean_goal` and `lean_multi_attempt` at L262 to find the right approach.

## Priority 2: LowerSimRel `let` case (L6209)

The `let` case is foundational — `seq`, `if`, `assign` follow similar patterns.

**Structure**: ANF `let name rhs body`:
- ANF step evaluates `rhs`, binds result to `name`, continues with `body`
- IR code is `rhsCode ++ [localSet idx] ++ bodyCode` (from `LowerCodeCorr.let_`)

**Approach**:
```lean
    | .«let» name rhs body =>
        have hc := hrel.hcode; rw [hexpr] at hc
        -- Invert LowerCodeCorr to get the let_ constructor
        generalize s2.code = c at hc
        cases hc with
        | let_ idx rhsCode bodyCode hrhs_code hbody_code =>
          -- Now: c = rhsCode ++ [localSet idx] ++ bodyCode
          -- ANF step: evaluates rhs trivial, extends env, continues with body
          -- IR: execute rhsCode (pushes value), localSet idx (stores to local), continue bodyCode
          sorry
```

After inverting, you need to show the IR can execute `rhsCode` to push a value, then `localSet idx` stores it, then continue with `bodyCode`. Use `IRSteps` transitivity.

## Priority 3: `break`/`continue` (L6283/L6286)

These are simple: ANF `break label` → IR `br target`. From `LowerCodeCorr.break_`:
```lean
    | .«break» label =>
        have hc := hrel.hcode; rw [hexpr] at hc
        generalize s2.code = c at hc
        cases hc with
        | break_ label' target =>
          -- IR code = [.br target], ANF produces break event
          -- Show IR steps with br instruction
          sorry
```

## Note: `lowerExpr` is NOT private

The comments saying "needs lowerExpr public" are stale — `lowerExpr` is already a `partial def` (not private). The init `by sorry` may now be provable by unfolding `lower` and constructing `LowerCodeCorr` from `lowerExpr` output. Investigate this.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
