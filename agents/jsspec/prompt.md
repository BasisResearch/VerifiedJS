# jsspec — ANF DEAD CODE FIX + CC INTEGRATION. Both are critical path.

## STATUS
- CC: 22 sorries (grep-c), ~20 actual. Proof agent active on value sub-cases.
- ANF: 17 sorries — ALL blocked by dead code absorption (your analysis confirmed this).
- Wasm: 11 actual sorries (wasmspec owns). DO NOT touch Semantics.lean.

## YOUR MISSION: TWO TRACKS

### TRACK 1: FIX ANF DEAD CODE ABSORPTION — TOP PRIORITY

Your analysis in `.lake/_tmp_fix/anf_break_continue_step_sim.lean` identified the root cause:
normalizeExpr CPS discards dead code after break/continue/throw/return,
but Flat.step? for .seq/.let continues executing it.

**Implement Fix D** (change Flat.step? to propagate errors through seq/let):
This is the cleanest fix. In Flat.step?, when stepping a sub-expression inside .seq or .let
produces an .error event, propagate the error immediately instead of continuing to the next part.

**Concrete changes needed** (in `VerifiedJS/Flat/Semantics.lean`):
```lean
-- In step? for .seq:
| .seq a b =>
    match step? { s with expr := a } with
    | some (.error msg, sa) => some (.error msg, { sa with expr := .lit .undefined })
    | some (t, sa) => ...  -- existing behavior
    | none => ...  -- existing behavior

-- In step? for .let:
| .let name rhs body =>
    match step? { s with expr := rhs } with
    | some (.error msg, sa) => some (.error msg, { sa with expr := .lit .undefined })
    | some (t, sa) => ...  -- existing behavior
    | none => ...  -- existing behavior
```

**IMPORTANT**: This will break ClosureConvertCorrect.lean proofs. You MUST:
1. Write the fix in `.lake/_tmp_fix/flat_error_propagation.lean` FIRST
2. Test with `lean .lake/_tmp_fix/flat_error_propagation.lean`
3. Document EXACTLY which CC proofs break and why
4. Only then discuss with supervisor whether to apply

### TRACK 2: CC INTEGRATION — Get staged files into the main proof

For every staged file that compiles, provide EXACT edit instructions:
```
INTEGRATION: <filename>
TARGET FILE: VerifiedJS/Proofs/ClosureConvertCorrect.lean
OLD: <exact old_string to match>
NEW: <exact new_string replacement>
```

Priority staged files:
1. `cc_state_mono.lean` → unblocks L2713, L2735, L4277, L4579
2. `cc_convertExpr_not_lit_v2.lean` → unblocks L1177-1178, L2200, L2310
3. `cc_exprAddrWF_propagate.lean` → unblocks L4230, L4328

### P1: Verify staged files still compile
Check these in `.lake/_tmp_fix/`:
- `cc_state_mono.lean`
- `cc_convertExpr_not_lit_v2.lean`
- `cc_exprAddrWF_propagate.lean`

## WORKFLOW
1. Read the relevant definitions first (`lean_hover_info`, `lean_local_search`)
2. Write standalone `.lean` files in `.lake/_tmp_fix/`
3. Test with `lean_run_code` or `lean_verify`
4. LOG every 30 min to agents/jsspec/log.md

## CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`, `VerifiedJS/Flat/Semantics.lean` (for Fix D ONLY after staging)
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- DO NOT run `lake build` (wastes time, proof agent is building)
