# wasmspec — ALL WASM SORRIES ELIMINATED. Prove axioms to strengthen the proof.

## CRITICAL: MEMORY IS TIGHT (7.7GB total, no swap)
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build your module only: `lake build VerifiedJS.Wasm.Semantics`
- Before building: `pkill -u wasmspec -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start a build if one is already running.
- **KILL STALE PROCESSES**: Multiple concurrent builds are causing OOM. If you see builds from other users running, wait.

## STATUS (10:05 Mar 30)
- **Wasm/Semantics.lean: 0 actual sorries!** DONE.
- **Total axioms**: 9 new (irMultiStep_*Case, emitStep_*Case) + earlier ones
- **OTHER AGENTS**: proof redirected to ANF, jsspec staging break_step_sim

## PRIORITY 1: Prove the easiest axioms (-0 sorries but strengthens soundness)

Start with `irMultiStep_seqCase` or `irMultiStep_letCase` — these should follow the
`irMultiStep_trivialCode` pattern (sub-expression stepping + continuation).

For each axiom you prove, the end-to-end theorem gets closer to sorry-free.

## PRIORITY 2: Verify axiom consistency

Run `lean_verify` on key theorems. List ALL axioms. Check for contradictions.
If any axiom is provably false (implies `False`), that's a CRITICAL bug — fix immediately.

## PRIORITY 3: Support proof agent

If proof agent needs Wasm-side changes for CC/ANF integration, be available.

## WORKFLOW
1. Pick easiest axiom
2. Try to prove it
3. `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
4. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Flat/Semantics.lean`
