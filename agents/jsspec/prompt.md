# jsspec — EXTEND Fix D to ALL compound expressions in Flat/Semantics.lean

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Flat.Semantics`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (12:05 Mar 30)
- **ANF**: 81 sorries. Break/continue decomposed. 66 compound sub-cases need Fix D.
- **CC**: 21 sorries.
- **Your staging file `.lake/_tmp_fix/fix_d_extension.lean` has EXACT before/after diffs.**

## YOUR CRITICAL TASK: Extend Fix D error propagation

Fix D currently exists for `.seq` (L391-392) and `.let` (L355-356) in `VerifiedJS/Flat/Semantics.lean`. When a sub-expression step produces `.error msg`, the compound expression should:
1. NOT wrap the error in a context step
2. Instead produce `.error msg` and set expr to `.lit .undefined`

### DO THIS IN ORDER (build after EACH one):

1. **`.assign name rhs`** (~L367-370): When `step? {s with expr := rhs}` = `some (.error msg, sr)`, produce error + .lit .undefined
2. **`.if cond then_ else_`** (~L379-382): Same for cond stepping
3. **`.unary op arg`** (~L403-406): Same for arg stepping
4. **`.typeof arg`** (~L411-414): Same for arg stepping
5. **`.binary op lhs rhs`** (~L420-430): For BOTH lhs and rhs stepping
6. **`.deleteProp obj prop`** (~L436-440): Same for obj stepping
7. **`.getProp obj prop`** (~L340-344): Same for obj stepping
8. **`.setProp obj prop val`** (~L346-352): For obj AND val stepping
9. **`.call f env args`**: For f, env, AND args stepping
10. **`.newObj f env args`**: Same as call
11. **`.getIndex obj idx`**: For obj and idx stepping
12. **`.setIndex obj idx val`**: For obj, idx, and val stepping
13. **`.throw arg`**: For arg stepping
14. **`.getEnv env`**: For env stepping
15. **`.makeClosure env ...`**: For env stepping
16. **`.makeEnv values`**: For values stepping
17. **`.objectLit props`**: For props stepping
18. **`.arrayLit elems`**: For elems stepping

### EXACT PATTERN (from your staging file):

For each compound expression's stepping match arm, change:
```lean
-- BEFORE:
| some (t, sr) => some (t, pushTrace { ... context step ... } t)
-- AFTER:
| some (.error msg, sr) => some (.error msg, pushTrace { s with expr := .lit .undefined, env := sr.env, heap := sr.heap } (.error msg))
| some (t, sr) => some (t, pushTrace { ... context step ... } t)
```

### AFTER EACH CHANGE:
```bash
pkill -f "lean.*\.lean" 2>/dev/null; sleep 5
lake build VerifiedJS.Flat.Semantics 2>&1 | tail -30
```

If the build breaks, fix the breakage BEFORE moving to next expression. The breakage will be in `step?_none_implies_lit_aux` — add a `next => simp at h` for the new error match arm.

### AFTER ALL Fix D extensions:
Build `lake build VerifiedJS.Proofs.ANFConvertCorrect` to check it still compiles.

## CONSTRAINTS
- CAN write: `VerifiedJS/Flat/Semantics.lean`, `.lake/_tmp_fix/*.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- LOG every 30 min to agents/jsspec/log.md
