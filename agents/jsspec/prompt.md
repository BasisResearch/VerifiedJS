# jsspec — Fix D extension + CC helper lemmas

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Flat.Semantics`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (14:05 Mar 30)
- **cc_hnoerr_guards.lean**: DONE ✓ (staging complete, 23 theorem diffs)
- **fix_d_extension.lean**: DONE ✓ (staging complete)
- **fix_d_proof_updates.lean**: DONE ✓
- wasmspec is applying hnoerr guards to CC NOW (was blocked by file permissions, now fixed)
- ANF: 17 sorries, CC: 22 sorries

## YOUR TASK: Apply Fix D extension to Flat/Semantics.lean

### Prerequisite check:
```bash
grep -c "hnoerr" VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
If count > 5, wasmspec has applied hnoerr guards → you can safely apply Fix D.
If count ≤ 2, WAIT — applying Fix D without hnoerr will break CC.

### Once prerequisite met: Apply Fix D
Your `.lake/_tmp_fix/fix_d_extension.lean` has the exact diffs. Apply them to `VerifiedJS/Flat/Semantics.lean`:
- Extend error propagation from seq/let (current) to ALL compound expressions
- This means: unary, binary, typeof, assign, call, newObj, getField, setField, getIndex, setIndex, delete, throw, return_some, yield_some, await, if (cond stepping), while (cond stepping)

Build after each group of 3-4 expressions: `lake build VerifiedJS.Flat.Semantics`

### If Fix D is NOT yet safe to apply:
Work on ANF helper staging instead:
1. Read ANFConvertCorrect.lean L4035-4068 (expression case sorries)
2. Stage proof sketches for `let` and `seq` cases in `.lake/_tmp_fix/anf_let_seq_proofs.lean`
3. These can help proof agent close those cases faster

### Also: Stage convertExpr_not_lit lemma
CC needs a `convertExpr_not_lit` lemma for L2513, L2623. Stage in `.lake/_tmp_fix/`:
```lean
theorem convertExpr_not_lit (e : Flat.Expr) (sc : CCState)
    (hne : ∀ v, e ≠ .lit v) :
    ∀ v, (Flat.convertExpr e sc).1 ≠ .lit v := by
  -- convertExpr preserves non-lit structure for non-stub constructors
  sorry -- sketch the proof approach
```

## FILES
- `VerifiedJS/Flat/Semantics.lean` (rw)
- `.lake/_tmp_fix/*.lean` (rw)
- DO NOT edit: `VerifiedJS/Proofs/*.lean`
- LOG every 30 min to agents/jsspec/log.md
