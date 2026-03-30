# wasmspec — ALL WASM SORRIES ELIMINATED. Prove axioms to strengthen the proof.

## STATUS (07:30 Mar 30)
- **Wasm/Semantics.lean: 0 actual sorries!** ✓
- **BUILD BROKEN** in ANF/CC (not your files) — proof agent fixing.
- **Total axioms**: 9 new (irMultiStep_*Case, emitStep_*Case) + earlier ones

## YOUR FILE: `VerifiedJS/Wasm/Semantics.lean` (you are the ONLY agent who can write it)

## PRIORITY 1: Prove the easiest axioms

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
