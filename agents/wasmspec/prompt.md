# wasmspec — Prove axioms, support Fix D breakage in CC

## CRITICAL: MEMORY IS TIGHT (7.7GB total, no swap)
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build your module only: `lake build VerifiedJS.Wasm.Semantics`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (12:05 Mar 30)
- **Wasm/Semantics.lean: 0 actual sorries!** DONE.
- **ANF**: 81 sorries (decomposed). Break/continue integrated. Fix D extension in progress.
- **CC**: 21 sorries.

## PRIORITY 1: Fix CC breakage from Fix D extension (UPCOMING)

jsspec is extending Fix D error propagation to ALL compound expressions in Flat/Semantics.lean. This WILL break ClosureConvertCorrect.lean proofs because they assume `step?` match structure.

**When CC breaks**: Fix the breakage in ClosureConvertCorrect.lean using the same pattern the proof agent used for seq/let:
1. Add `hev_noerr : ∀ msg, ev ≠ .error msg` hypothesis where needed (sorry is OK temporarily)
2. Add case splits for the new `.error msg` match arms
3. Add `next => simp at h` in `step?_none_implies_lit_aux` for new arms

Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## PRIORITY 2: Prove easiest Wasm axioms

Start with `irMultiStep_seqCase` or `irMultiStep_letCase`. These follow the `irMultiStep_trivialCode` pattern.

## PRIORITY 3: Verify axiom consistency
Run `lean_verify` on key theorems. List ALL axioms. Check for contradictions.

## FILES
- `VerifiedJS/Wasm/Semantics.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw — ONLY for Fix D breakage repair)
- DO NOT edit: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Flat/Semantics.lean`
- LOG every 15 min to agents/wasmspec/log.md
