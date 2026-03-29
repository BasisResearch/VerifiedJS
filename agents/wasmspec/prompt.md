# wasmspec — RESTART: SMALL WINS FIRST

## STATUS: 63 grep sorries (18 Wasm). Build passes. You've been running 4+ hours with no output — likely OOM.

**Your previous runs keep getting killed (code 137/143). You MUST work in smaller increments.**

## PRIORITY 0: Fix `hlabels_empty` invariant (UNBLOCKS 3 sorries)

This is your #1 task. Do NOT attempt anything else until this is done or documented as impossible.

Current problem: `LowerSimRel` has `hlabels_empty : s2.labels = []` but break/continue/labeled
REQUIRE non-empty labels.

**Step 1**: Find the `LowerSimRel` definition. `grep -n "LowerSimRel" VerifiedJS/Wasm/Semantics.lean | head -10`

**Step 2**: Analyze options:
- A) Change to `hlabels_match : s2.labels.length = labelDepth expr` — tracks nesting
- B) Remove `hlabels_empty` entirely — prove label correctness case-by-case
- C) Keep `hlabels_empty` for top-level, add `LowerSimRel_labeled` variant

**Step 3**: Pick simplest. Implement. Verify `lake env lean VerifiedJS/Wasm/Semantics.lean` passes.

**Step 4**: If the change breaks other things, sorry them and document. Better to have 20 sorries
with a correct invariant than 18 with a wrong one.

## PRIORITY 1: Close `return none` step_sim fully

`step_sim_return_none` should be the easiest case (1:1 stepping, already partially done).
If there's any remaining sorry in that case, close it.

## CRITICAL: WORK IN SMALL INCREMENTS
- Edit < 50 lines at a time
- Build-check after EVERY edit
- Log progress after EVERY successful build
- Do NOT attempt multi-hour proof sessions — you will OOM

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw), `VerifiedJS/ANF/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
## LOG: agents/wasmspec/log.md
