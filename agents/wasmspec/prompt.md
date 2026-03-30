# wasmspec — Apply hnoerr guards to CC + close CC sorries

## CRITICAL: MEMORY IS TIGHT (7.7GB total, no swap)
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build your module: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (13:05 Mar 30)
- **Wasm/Semantics.lean: 0 actual sorries!** DONE. ✓
- **ANF**: 17 sorries (proof agent handling)
- **CC**: 22 actual sorries — YOUR MAIN TARGET NOW

## PRIORITY 1: Add hnoerr guards to Flat_step?_*_step theorems

jsspec is staging the exact diffs, but you can start NOW. The ~20 `Flat_step?_*_step` theorems in ClosureConvertCorrect.lean (L1620-2081) need a `hnoerr : ∀ msg, t ≠ .error msg` hypothesis added.

### Why: Fix D preparation
Fix D error propagation will change Flat.step? so that error events in sub-expressions propagate instead of being wrapped in compound contexts. The current theorems are incorrect for error events. Adding `hnoerr` makes them correct both before AND after Fix D.

### How:
For each theorem like `Flat_step?_unary_step`, `Flat_step?_typeof_step`, etc.:
1. Add `(hnoerr : ∀ msg, t ≠ .error msg)` as last hypothesis
2. The proof body likely still works (`simp only [Flat.step?, hnv, hss]; rfl`)
3. At each CALL SITE, supply the `hnoerr` proof. Usually you can get it from context (the CC simulation maintains that trace events from well-formed expressions are not errors until the expression itself throws).

### Important: Some call sites may not have `hnoerr` available!
If a call site can't easily prove `hnoerr`:
- Check if the event actually CAN be an error there. If not, prove it from context.
- If proving is hard, add `by sorry` temporarily with comment `-- hnoerr: needs proof`
- This is OK — we're unblocking Fix D, which will close more sorries than it creates.

Build after EVERY 2-3 theorem changes: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## PRIORITY 2: Close CC sorries (in parallel with P1)

Pick off the easier CC sorries:

### Tier A (mechanical):
- **L2707**: standalone sorry — read context, likely simple
- **L3036, L3058**: CCState threading — pattern match on state, use `convertExpr_state_determined`
- **L5018**: CCState threading for while_ — similar pattern

### Tier B (need helper lemmas):
- **L2852, L3175**: `hev_noerr` — prove event is not error from context
- **L4669, L4767**: ExprAddrWF propagation — need `ExprAddrPropListWF`/`ExprAddrListWF`
- **L2513, L2623**: need `convertExpr_not_lit` for stub constructors

### Tier C (hard):
- **L1369, L1370**: forIn/forOf stubs — likely unprovable (converts to `.lit .undefined`)
- **L3562, L3563**: call/newObj value sub-cases
- **L4131**: getIndex string both-values (semantic mismatch)
- **L4303, L4625, L4723**: value sub-cases needing heap reasoning
- **L4897**: functionDef
- **L4987**: tryCatch

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Wasm/Semantics.lean` (rw — no changes needed)
- DO NOT edit: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Flat/Semantics.lean`
- LOG every 15 min to agents/wasmspec/log.md
