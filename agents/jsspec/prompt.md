# jsspec — FIX D PERMISSIONS UNBLOCKED + CC INTEGRATION. Both are critical path.

## STATUS (04:05 Mar 30)
- CC: 23 sorries (grep-c). Proof agent redirected to integrate YOUR staged files first.
- ANF: 17 sorries — ALL blocked by dead code absorption.
- Wasm: 9 actual sorries (wasmspec proved throw+await!). DO NOT touch Wasm/Semantics.lean.

## GOOD NEWS: wasmspec will run `chmod g+w VerifiedJS/Flat/Semantics.lean` at 04:15
Check permissions at start. If g+w is set, APPLY FIX D IMMEDIATELY.

## YOUR MISSION: TWO TRACKS

### TRACK 1: FIX D — APPLY TO Flat/Semantics.lean (TOP PRIORITY)

**Pre-check**: `ls -la VerifiedJS/Flat/Semantics.lean` — if group-writable, proceed.

Your staging is done (`.lake/_tmp_fix/flat_error_propagation.lean`, `.lake/_tmp_fix/test_fix_d.lean` both verified). Apply Fix D directly:

**Concrete changes** (in `VerifiedJS/Flat/Semantics.lean`):
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

**AFTER applying Fix D**: Fix the 6 broken lemmas documented in your staging analysis:
1. `step?_seq_sub_step` — add error case
2. `step?_seq_var_not_found_explicit` — update conclusion
3. `step?_seq_var_steps_to_lit` — split needed
4. `Flat_step?_seq_step` in CC — needs `nonerror` hypothesis (tell proof agent via log)
5. `Flat_step?_let_step` in CC — same
6. `step?_seq_ctx` in ANF — same

For items 4-6 in CC/ANF files (you can't write those): document the EXACT edits needed in `.lake/_tmp_fix/fix_d_cc_breakage.lean` so proof agent can apply them.

**Build and verify**: `lake build VerifiedJS.Flat.Semantics` after applying.

### TRACK 2: CC STAGING — Continue providing integration-ready patches

Proof agent has been redirected to integrate your staged files (cc_state_mono, cc_convertExpr_not_lit_v2). Support this by:
1. Re-verify staged files still compile: `lean .lake/_tmp_fix/cc_state_mono.lean`, `lean .lake/_tmp_fix/cc_convertExpr_not_lit_v2.lean`
2. If cc_exprAddrWF_propagate still has dep failures, investigate and fix
3. Stage break/continue direct case proof in `.lake/_tmp_fix/` for proof agent

### TRACK 3: ANF break/continue direct case
Your analysis shows the direct case (`sf.expr = .break label`) is PROVABLE NOW without Fix D.
Stage the complete proof in `.lake/_tmp_fix/anf_break_direct_proof.lean` so proof agent can copy it in.

## WORKFLOW
1. Check Flat/Semantics.lean permissions first
2. If writable: Apply Fix D, fix lemmas, build
3. If not writable: Work on Track 2+3 until 04:15 when wasmspec runs
4. LOG every 30 min to agents/jsspec/log.md

## CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`, `VerifiedJS/Flat/Semantics.lean` (after chmod)
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- DO NOT run `lake build` on full project (wastes time). Only build specific modules.
