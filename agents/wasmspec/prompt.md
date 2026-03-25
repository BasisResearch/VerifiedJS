# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 24 (in Semantics.lean)

### PROVABLE NOW (no label stack needed)

**Priority 1: return (some t) — L6271**

Follows the `return none` pattern (L6237-6270). LowerCodeCorr is `return_some arg argCode`, so IR code = `argCode ++ [.return_]`. ANF `return (some t)` evaluates `t` via `evalTrivial`, produces `.silent`. Use `step?_return_some_ok`.

```lean
    | some t =>
        have hc := hrel.hcode; rw [hexpr] at hc
        generalize s2.code = c at hc
        cases hc with
        | return_some arg argCode =>
          -- argCode evaluates the trivial, then return_
          -- ANF step: evalTrivial env t = .ok v → (.silent, pushTrace ... .silent)
          -- IR: execute argCode (pushes value), then return_ (pops frame)
          -- Use IRSteps_trans for the 2-step sequence
          sorry
```

**Priority 2: readLE? (L262) — provable**

Goal: `readLE? mem addr width = none` given `mem.size = 0`, `0 < width`.
The `for k in [0:width]` loop hits `¬(addr + 0 < mem.size)` on first iteration (k=0), returning `none`. Try unfolding `readLE?` and working with the `Std.Range.forIn` loop. This may need a custom lemma about `forIn` on `[0:width]` when the body returns `ForInStep.done` on first iteration.

**Priority 3: throw (L6227)**

ANF `throw arg` evaluates `arg` and produces `.error`. Similar to return.

### BLOCKED (need label stack correspondence)

**LowerSimRel has `hlabels_empty : ir.labels = []`**, which makes break/continue/while/labeled UNPROVABLE — they all need labels on the stack. To unblock:

Replace `hlabels_empty` with a label stack correspondence:
```lean
/-- Labels on the IR stack correspond to enclosing control structures in ANF. -/
hlabels : LabelStackCorr s.expr ir.labels
```

Where `LabelStackCorr` is a new inductive relating ANF nesting to IR label stack. This is architectural — do NOT attempt until return/throw are closed.

Blocked cases: L6209(let), L6217(seq), L6221(if), L6224(while), L6230(tryCatch), L6274(yield), L6277(await), L6280(labeled), L6283(break), L6286(continue)

### EmitSimRel cases (8 sorries)
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

### Init (3 `by sorry`)
```
L8888  LowerSimRel.init by sorry
L8903  LowerSimRel.init by sorry
L8927  LowerSimRel.init by sorry
```

These need `LowerCodeCorr` for the initial program, which requires `lowerExpr` to be public.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
