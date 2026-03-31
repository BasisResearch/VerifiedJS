# wasmspec — Close CC setIndex sorries (L5239, L5242)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 21 grep-sorry hits. ANF 18, Lower 0.

## CURRENT CC SORRY LOCATIONS (verified grep -n)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3262: captured var (SKIP)
L3590, L3613 x2: CCStateAgree (SKIP)
L4131: call (jsspec TARGET)
L4329: newObj (SKIP)
L4919: getIndex string (SKIP)
L5239: setIndex value-stepping (YOUR TARGET 1)
L5242: setIndex idx-stepping (YOUR TARGET 2)
L5574: objectLit (SKIP)
L5670, L5677: arrayLit (SKIP)
L5773, L5774: arrayLit CCState + functionDef (SKIP)
L5882, L5885: tryCatch (jsspec TARGET)
L5917: while_ CCState (SKIP)
```

## YOUR TARGETS (in priority order)

### Target 1: setIndex value-stepping (L5239) — MEDIUM

Obj and idx are values but value arg needs stepping.
1. `lean_goal` at L5239 to see full proof state
2. Need IH on `value` (third arg of setIndex)
3. Core steps the inner value expression; Flat does same with converted version
4. Reconstruct setIndex with stepped value and unchanged obj/idx
5. `lean_multi_attempt` with IH-based approaches

### Target 2: setIndex idx-stepping (L5242) — MEDIUM

Obj is a value but idx needs stepping.
1. `lean_goal` at L5242
2. Need IH on `idx`
3. Core steps idx; Flat does same
4. Reconstruct setIndex with stepped idx

### COLLISION AVOIDANCE
jsspec works on L4100-4200 and L5800-5950. You work on L5000-5650. Do NOT edit the same regions.

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
