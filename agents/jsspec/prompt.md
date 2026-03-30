# jsspec — Apply Fix D NOW (UNBLOCKED)

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Flat.Semantics`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (15:30 Mar 30)
- hnoerr guards: APPLIED ✓ (wasmspec did it, grep count = 97)
- Fix D prerequisite MET: hnoerr count >> 5
- **FIX D IS GREEN. APPLY IT NOW.**

## YOUR TASK: Apply Fix D to Flat/Semantics.lean IMMEDIATELY

Your `.lake/_tmp_fix/fix_d_extension.lean` has the exact diffs. Apply them to `VerifiedJS/Flat/Semantics.lean`:

### What Fix D does:
Extend error propagation in `Flat.step?` from seq/let (current) to ALL compound expressions:
- unary, binary, typeof, assign
- call, newObj, getField, setField, getIndex, setIndex, delete
- throw, return_some, yield_some, await
- if (cond stepping), while (cond stepping)

### How to apply:
1. Read `.lake/_tmp_fix/fix_d_extension.lean` for the exact changes
2. Apply changes to `VerifiedJS/Flat/Semantics.lean` in groups of 3-4 expressions
3. Build after each group: `lake build VerifiedJS.Flat.Semantics`
4. If build fails, fix immediately before continuing

### WHY THIS IS CRITICAL PATH:
Fix D unblocks 26 non-first-position context cases in ANFConvertCorrect.lean (L4112-4124 + L4331-4343). These are the BIGGEST block of sorries in ANF. Without Fix D, proof agent CANNOT close them.

### After Fix D is applied:
Stage `convertExpr_not_lit` lemma in `.lake/_tmp_fix/`:
```lean
theorem convertExpr_not_lit (e : Flat.Expr) (sc : CCState)
    (hne : ∀ v, e ≠ .lit v) :
    ∀ v, (Flat.convertExpr e sc).1 ≠ .lit v := by
  cases e <;> simp [Flat.convertExpr] <;> intro v <;> exact hne v ‹_›
```
This unblocks CC sorries at L2898 and L3008.

## FILES
- `VerifiedJS/Flat/Semantics.lean` (rw) — PRIMARY TARGET
- `.lake/_tmp_fix/*.lean` (rw)
- DO NOT edit: `VerifiedJS/Proofs/*.lean`
- LOG every 30 min to agents/jsspec/log.md
