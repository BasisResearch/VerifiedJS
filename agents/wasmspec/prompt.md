# wasmspec — Reformulate hasBreakInHead/hasContinueInHead theorems

## Your analysis was EXCELLENT. break_direct/continue_direct proofs are solid.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean (coordinate with proof agent on L6700-6800)

## STATE: 8 ANF sorries in hasBreak/hasContinue compound cases (L6751-6784). All FALSE as stated.

## YOUR ANALYSIS RECAP:
- break_direct/continue_direct: PROVED ✓
- Compound cases (seq_left, seq_right, let_init, wildcard): FALSE because:
  1. `.seq (.break l) b` → b still evaluates → final expr ≠ `.lit .undefined`
  2. `.assign "x" (.break l)` → env modified
  3. `.let "y" (.break l) body` → body evaluates with modified env
- While loops with break in body ARE reachable from normalizeExpr output
- So the compound cases CANNOT be eliminated by contradiction

## YOUR TASK: Reformulate the theorems

The current theorems promise too much for compound cases. The fix is to WEAKEN the conclusion for compound HasBreakInHead.

### Option A: Split into two theorems (RECOMMENDED)

Replace the current monolithic theorem with:

1. **Direct case** (already proved): keep as-is
2. **Compound case**: weaker conclusion — only promise the error event appears in the trace, NOT that the final expression is `.lit .undefined`

```lean
/-- For compound HasBreakInHead, the break error event eventually appears in the trace,
    but the final expression state depends on the surrounding context. -/
private theorem hasBreakInHead_flat_error_trace
    (hbreak : HasBreakInHead e label)
    (hbreak_compound : ¬∃ l, e = .break l) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs sf' ∧
      .error ("break:" ++ label.getD "") ∈ evs.join ∧
      sf'.env = env ∨ True  -- weaken env/heap preservation claims
```

Wait — check what the DOWNSTREAM code actually NEEDS from this theorem. Read:
- `grep -n "hasBreakInHead_flat_error_steps" VerifiedJS/Proofs/ANFConvertCorrect.lean`
- Look at all call sites (should be in anfConvert_step_star around L7757-8015)
- Determine what properties the callers actually USE from the result

### Step 1: Find all callers
```
grep -n "hasBreakInHead_flat_error_steps\|hasContinueInHead_flat_error_steps" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

### Step 2: For each caller, determine what it needs:
- Does it use `sf'.expr = .lit .undefined`?
- Does it use `sf'.env = sf.env`?
- Does it use `sf'.heap = sf.heap`?
- Does it only use the error trace event?

### Step 3: Reformulate to provide EXACTLY what callers need

If callers only need the error trace event + multi-step relationship, reformulate accordingly. If callers need expression equality, the caller needs to be restructured too.

### Step 4: Implement the reformulated theorem
- Prove it by induction on HasBreakInHead
- break_direct: use existing proof
- Compound cases: use eval context stepping (step?_seq_ctx etc.) + IH

### Step 5: Update callers to use the new theorem

### Alternative: normalizeExpr_break_only_direct

If investigation shows normalizeExpr output (with trivial-preserving k) ONLY produces HasBreakInHead via while loops, and while loops with break are handled separately in the proof, then maybe the compound cases in hasBreakInHead_flat_error_steps are UNREACHABLE from anfConvert_step_star.

Check: does anfConvert_step_star call hasBreakInHead_flat_error_steps on normalizeExpr output? If so, can we prove that normalizeExpr output only has break_direct (excluding .seq (.while_ ...) patterns)?

This would be:
```lean
theorem normalizeExpr_break_only_via_while
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (e', m))
    (hk : trivial_preserving k)
    (hbreak : HasBreakInHead e' label) :
    (∃ l, e' = .break l) ∨
    (∃ c d b, e' = .seq (.while_ c d) b ∧ HasBreakInHead (.while_ c d) label)
```

If this is provable, then anfConvert_step_star only needs break_direct + while-break, both of which can be handled separately.

## Build command
`lake build VerifiedJS.Proofs.ANFConvertCorrect`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
