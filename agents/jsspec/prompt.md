# jsspec — CREATE ANFInversion.lean (4TH CONSECUTIVE FAILURE)

## STATUS: 62 grep sorries. ANFInversion.lean STILL DOES NOT EXIST in the main tree.

## YOU HAVE BEEN TOLD TO DO THIS FOR 4 CONSECUTIVE RUNS. THE PROOF AGENT CANNOT USE YOUR WORK.

## PRIORITY 0: Create `VerifiedJS/Proofs/ANFInversion.lean` — DO IT IN THE FIRST 5 MINUTES

The staging file EXISTS at `.lake/_tmp_fix/VerifiedJS/Proofs/ANFInversion.lean`.

Steps:
1. Read `.lake/_tmp_fix/VerifiedJS/Proofs/ANFInversion.lean` (it's already complete)
2. Copy it to `VerifiedJS/Proofs/ANFInversion.lean`
3. Run `lake build VerifiedJS.Proofs.ANFInversion`
4. If it fails on imports, check what `VerifiedJS/Proofs/ANFConvertCorrect.lean` imports and match
5. If it fails on definitions, check if the types changed since staging was written

That's it. 5 lines of shell commands. Do not overthink it.

## PRIORITY 1: After ANFInversion.lean builds, add import to ANFConvertCorrect.lean

Add `import VerifiedJS.Proofs.ANFInversion` to the import list of `ANFConvertCorrect.lean`.
Then build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## PRIORITY 2: Complete the 5 missing list-based constructor cases in break characterization

From your log (2026-03-29T00:00): call, newObj, makeEnv, objectLit, arrayLit need
normalizeExprList/normalizeProps characterization. These are in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`.

## FILES
- `VerifiedJS/Proofs/ANFInversion.lean` (CREATE THIS)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (add import only)
- `.lake/_tmp_fix/` (read only — source material)

## DO NOT EDIT: `VerifiedJS/Proofs/ClosureConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md — LOG THE FILE CREATION IMMEDIATELY
