# wasmspec — Close CC objectLit/arrayLit all-values heap sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 17 actual sorry lines. You previously closed objectLit all-values and 2 setIndex sorries. Excellent work.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 03:05)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3320: HeapInj refactor (SKIP)
L3648, L3671 x2: CCStateAgree (SKIP)
L4189: call function (BLOCKED)
L4387: newObj (SKIP)
L4977: getIndex string (SKIP)
L5807: objectLit all-values (YOUR TARGET 1 — you left a sorry here)
L5982: objectLit CCState sub-step (jsspec TARGET)
L5989: arrayLit all-values heap (YOUR TARGET 2)
L6085: arrayLit CCState sub-step (jsspec TARGET)
L6086: functionDef (SKIP)
L6213, L6243, L6246: tryCatch (jsspec TARGET)
L6278: while_ CCState (SKIP)
```

## YOUR TARGETS

### Target 1: objectLit all-values — finish the sorry at L5807
You partially expanded this proof but left a sorry at L5807. You have the HeapInj pattern from
your previous objectLit success. The proof structure around L5807 already has:
- `simp [Flat.step?, hvs, Flat.step?_pushTrace_expand] at hstep`
- `obtain ⟨rfl, rfl⟩ := hstep`
- Then sorry

After the simp/obtain, you need:
- Construct the Core step (Core.step?_objectLit_val)
- Show HeapInj for the new heap (HeapInj_alloc_both)
- Show EnvCorrInj preservation
- Show trace/env/heap relationships

Look at the proof just below L5807 (L5808-5850) — you already wrote the Core side setup.
The sorry replaces the actual refine/construction. Connect your setup to the conclusion.

### Target 2: arrayLit all-values heap (L5989)
Same pattern as objectLit all-values. After finishing Target 1, adapt the proof.

### COLLISION AVOIDANCE
You work on L5000-5989. jsspec works on L5982-6280.
Do NOT edit L5982+ (that's jsspec territory). L5989 is your last line.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
