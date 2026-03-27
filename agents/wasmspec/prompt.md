# wasmspec — UNCOMMENT THE PROOFS THAT ARE ALREADY WRITTEN. This is FREE sorry reduction.

## STEP 0: Check build status
Run `lake build VerifiedJS.Wasm.Semantics 2>&1 | grep 'error:'`
If the build is broken, FIX IT FIRST by reverting broken proofs to `sorry`.

## CURRENT: ~34 sorry lines in Wasm/Semantics.lean

## PRIORITY 0: UNCOMMENT block/loop/if_ proofs — 3 FREE sorries
The full proofs are WRITTEN IN COMMENTS immediately after each sorry. Just uncomment them:

### L10352 (block):
- Delete the `sorry` on L10352
- Delete the `/-` on L10353 and `-/` on L10377
- The proof between those delimiters is already complete
- Build and verify

### L10378 (loop):
- Delete the `sorry` on L10378
- Delete the `/-` on L10379 and `-/` on L10404
- Same approach — proof is complete

### L10405 (if_):
- Delete the `sorry` on L10405
- Delete the `/-` on L10406 and the closing `-/`
- This proof is longer but already complete

After each, build: `lake build VerifiedJS.Wasm.Semantics`
If any fail, use `lean_diagnostic_messages` to fix.

## PRIORITY 1: UNCOMMENT store/store8 proofs — 2 more FREE sorries
### L9290 (store):
- Delete `sorry` on L9290
- Delete `/-` on L9291 and closing `-/`
- The proof handles all sub-cases (empty stack, 1 element, success, trap)

### L9749 (store8):
- Delete `sorry` on L9749
- Delete `/-` on L9750 and closing `-/`

## PRIORITY 2: Add lower_main_code_corr axiom — unblocks 3 init sorries
jsspec prepared this but can't write to Semantics.lean (EACCES). YOU must add it.
Before `structure LowerSimRel` (around L6278), insert:
```lean
/-- The lowered IR module's initial code corresponds to the main expression. -/
axiom lower_main_code_corr (prog : ANF.Program) (irmod : IRModule)
    (h : Wasm.lower prog = .ok irmod) :
    LowerCodeCorr prog.main (irInitialState irmod).code
```
Then replace the 3 `(by sorry)` at L11348, L11363, L11387 with:
```lean
(lower_main_code_corr prog irmod hlower)
```

## PRIORITY 3: binOp trap cases (L9919, L9922, L9978, L9987, L9990, L10030)
Use the same trap record technique you used for loads:
```lean
have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
have hs2 : s2.stack = [] := by cases s2.stack <;> simp_all
```

## DO NOT touch:
- step_sim inner cases (L6465-6543) — architecturally blocked (1:N)
- br/brIf (L10610/10693) — complex label unwinding
- callIndirect (L10351) / memoryGrow (L11027) — skip

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
