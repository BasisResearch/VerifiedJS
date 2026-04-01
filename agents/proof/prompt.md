# proof — Prove normalizeExpr_return_step_sim, then yield

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 20 sorries. Lower 0 ✓. CC — OTHER AGENTS OWN IT.

## EXCELLENT PROGRESS: HasReturnInHead infrastructure DONE ✓
You have built:
- `HasReturnInHead` inductive (L4103-4131)
- `normalizeExpr_return_or_k` lemmas (through L4851+)
- `normalizeExpr_return_implies_hasReturnInHead` (L4878)
- `normalizeExpr_return_step_sim` DEFINED at L5466 but body is SORRY (L5493)
- The main theorem's return case (L5942+) already USES normalizeExpr_return_step_sim — it works!

## YOUR IMMEDIATE TASK: Prove normalizeExpr_return_step_sim (L5493)

The theorem is at L5466-5493. It takes `hnorm`, `hk` (trivial-preserving k), `hewf` and produces 3 conjuncts:
1. `arg = none` → return without argument
2. `∀ t v, arg = some t → evalTrivial ok` → return with successful arg
3. `∀ t msg, arg = some t → evalTrivial error` → return with failed arg

**Strategy**: Apply the EXACT SAME pattern as your await_step_sim proof:
1. Use `normalizeExpr_return_implies_hasReturnInHead` to get `HasReturnInHead sf.expr`
2. Induction on `HasReturnInHead sf.expr`
3. For each constructor:
   - `return_none_direct`: Flat.step? on .return none → trivially produces the required events
   - `return_some_direct`: Flat.step? on .return (some v) → evaluate v, produce events
   - `seq_left`, `let_init`, etc.: decompose, use IH

**Key helpers you already have from await work:**
- `Flat.step?_await_lit_eq`, `Flat.step?_await_var_ok`, `Flat.step?_await_this_ok`
- Analogues for return: you need `Flat.step?_return_none_eq` and `Flat.step?_return_some_eq`
  Build these first if they don't exist!

```lean
-- Template:
private theorem Flat.step?_return_none_eq (env : Flat.Env) (heap : Core.Heap)
    (trace : List Core.TraceEvent) (funcs : Array Flat.FuncDef) (cs : List Flat.Env) :
    Flat.step? ⟨.return none, env, heap, trace, funcs, cs⟩ =
    some (.error "return:undefined",
      ⟨.lit .undefined, env, heap, trace ++ [.error "return:undefined"], funcs, cs⟩) := by
  unfold Flat.step?; rfl
```

### Priority 2: After L5493 is done, build HasYieldInHead + yield_step_sim
Same pattern. Copy HasReturnInHead → HasYieldInHead. Build yield helpers.

### Priority 3: Compound cases (L5097, L5128, L5139, L5217, L5248, L5259, L5276)
These are "non-labeled inner value" and "compound/bindComplex" cases. They need depth induction.

## DO NOT ATTEMPT:
- GROUP B (architecturally blocked)
- hasBreak/ContinueInHead (L5293, L5306) — potentially unprovable as stated

## CURRENT ANF SORRY LOCATIONS (file is 7562 lines):
```
Decomposed await: L5097, L5128, L5139, L5217, L5248, L5259, L5276
hasBreak/ContinueInHead: L5293, L5306
await flat_arg compound: L5459, L5462
return_step_sim BODY: L5493 (YOUR #1 TARGET)
await inner_arg: L5656, L5663, L5666
yield/seq/if/let/tryCatch: L5697, L5718, L5739, L5760, L5781
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
