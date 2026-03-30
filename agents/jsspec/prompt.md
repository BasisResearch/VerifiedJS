# jsspec — Prepare hnoerr guards for Fix D, stage CC helper lemmas

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Flat.Semantics`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (13:05 Mar 30)
- **ANF**: 17 sorries (down from 81!). Break/continue compound sub-cases ALL closed.
- **CC**: 22 actual sorries.
- **Fix D extension**: BLOCKED — you correctly identified that Flat_step?_*_step theorems need hnoerr guards first.

## SITUATION: Fix D dependency chain
1. ClosureConvertCorrect.lean has ~20 `Flat_step?_*_step` theorems (L1620-2081) that assume context-wrapping for ALL trace events including errors
2. Fix D changes error behavior: error events propagate instead of wrapping
3. These theorems need `hnoerr : ∀ msg, t ≠ .error msg` hypothesis added
4. THEN Fix D can be applied to Flat/Semantics.lean

## YOUR TASK: Stage the hnoerr guard changes

### Task 1: Create staging file with EXACT CC hnoerr diffs
Create `.lake/_tmp_fix/cc_hnoerr_guards.lean` with the exact before/after for each `Flat_step?_*_step` theorem in ClosureConvertCorrect.lean.

For each theorem (there are ~20 at L1620-2081), the change is:
```lean
-- BEFORE:
private theorem Flat_step?_unary_step (s : Flat.State) (op : Core.UnaryOp) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    ...

-- AFTER:
private theorem Flat_step?_unary_step (s : Flat.State) (op : Core.UnaryOp) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hnoerr : ∀ msg, t ≠ .error msg) :  -- NEW
    ...
```

The proofs should still work with `simp only [Flat.step?, hnv, hss]; rfl` because the non-error case is unchanged.

BUT: every CALL SITE of these theorems must also supply `hnoerr`. Stage the call site changes too.

### Task 2: Stage CC sorry-closing lemmas

Several CC sorries are in known classes. Stage proofs for the easiest ones:

1. **hev_noerr sorries** (L2852, L3175): `have hev_noerr : ∀ msg, ev ≠ .error msg := by sorry`
   - These need to prove that the CC-simulated event is not an error
   - Check what `ev` is in context — it comes from a Core.step that doesn't produce errors in these positions

2. **ExprAddrWF propagation** (L4669, L4767): needs `ExprAddrPropListWF` / `ExprAddrListWF`
   - Stage these helper lemmas

3. **convertExpr_not_lit** (L2513, L2623): stage the lemma

### Task 3: Update fix_d_extension.lean staging

Your existing `fix_d_extension.lean` is good. Update it to note:
- Step 1 (prerequisite): Apply hnoerr guards from `cc_hnoerr_guards.lean`
- Step 2: Apply Fix D changes
- Step 3: Update `step?_none_implies_lit_aux` for new arms

## CONSTRAINTS
- CAN write: `VerifiedJS/Flat/Semantics.lean`, `.lake/_tmp_fix/*.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- LOG every 30 min to agents/jsspec/log.md
