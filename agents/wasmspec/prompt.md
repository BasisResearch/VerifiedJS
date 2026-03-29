# wasmspec — UNBLOCK STEP_SIM: FIX HLABELS_EMPTY + 1:N FRAMEWORK

## STATUS: 59 grep sorries (18 Wasm). Build PASSES. All 12 step_sim cases identified as BLOCKED.

Your previous analysis correctly identified three structural blockers:
1. `hlabels_empty` prevents break/continue/labeled
2. `hframes_one` prevents call
3. 1:1 framework prevents all 1:N cases (let, seq, if, while, throw, tryCatch, yield, await, return some)

**Strategy shift: instead of trying to close sorries, UNBLOCK them by fixing the infrastructure.**

## PRIORITY 0: Fix `hlabels_empty` to unblock break/continue/labeled (-3 potential)

The `LowerSimRel` has `hlabels_empty : s2.labels = []`. But break/continue/labeled REQUIRE labels to be non-empty (that's how they work in Wasm — `br` targets a label index).

**Analysis needed**: Look at how `Lower.lean` lowers `.labeled label body`:
1. Find `lowerExpr` case for `.labeled` — it likely emits `IRInstr.block label bodyCode`
2. `IRInstr.block` pushes a label when stepped, so labels become non-empty
3. The invariant should be: labels = [] at TOP LEVEL, but inside labeled blocks, labels reflect nesting

**Fix options**:
A. Change `hlabels_empty` to `hlabels_match : s2.labels.length = labelDepth s1.expr` (tracks label nesting)
B. Remove `hlabels_empty` from LowerSimRel entirely and prove label correspondence separately
C. Keep `hlabels_empty` but add a separate `LowerSimRel_labeled` for inside-block states

Pick whichever is simplest. The key insight: break/continue are only reachable INSIDE a labeled block, so the labels invariant only matters in the labeled sub-proof.

## PRIORITY 1: Design 1:N stepping framework

Currently `step_sim` proves: 1 ANF step → 1 IR step. But most cases need 1:N (one ANF step → N IR steps). The `return none` case already works because it's genuinely 1:1.

For 1:N, you need a stuttering simulation. You already have `step_sim_return_litNull` (L6881) as a 1:2 template. Generalize:

```lean
theorem step_sim_general (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (hrel : LowerSimRel prog irmod s1 s2)
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      traceFromCore t = traceConcat ir_trace ∧
      LowerSimRel prog irmod s1' s2'
```

Where `IRSteps` is a reflexive-transitive closure of `irStep?`. This lets each case take as many IR steps as needed.

## PRIORITY 2: Close throw/break/continue if unblocked

If P0 succeeds in fixing labels:
- **break**: ANF produces `.error ("break:" ++ label)`. IR does `br labelIdx`. Use `LowerCodeCorr.break_inv` to get IR shape. Show `traceFromCore (.error ("break:" ++ label)) = .silent` (already proved). Show IR `br` produces `.silent`.
- **continue**: Same pattern.
- **throw**: ANF produces `.error msg`. IR does `throw_`. Show traces match.

## FILES: `VerifiedJS/ANF/Semantics.lean` (rw), `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
## LOG: agents/wasmspec/log.md
