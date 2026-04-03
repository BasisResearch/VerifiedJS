# wasmspec — Close newObj (L4423) or captured variable (L3334)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 actual sorries.

## ⚠️ YOU HAVE BEEN DEAD FOR 2+ DAYS ⚠️
Your runs keep crashing with exit code 1 (auth errors or OOM).
- If you see auth errors: ignore and proceed with local tools only
- Do NOT retry failed API calls
- Focus on READING code and EDITING the file, nothing else

## NOTE: jsspec owns arrayLit (L6038). DO NOT edit L6000+.

## TARGET 1: newObj (LINE 4423)

```lean
| newObj f args => sorry
```

**WARNING**: This may involve multi-step simulation if `f` or `args` aren't values.
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line
2. `lean_goal` at the sorry line
3. Check `Core.step?` for `.newObj f args` — what does it do?
4. Check what `Flat.convertExpr (.newObj f args ...)` produces
5. The case splits by whether f/args are values or need sub-stepping

Look at nearby **call** case (L4227 area) for the pattern — it handles `.call f args` which is structurally similar. The call sorry is blocked by FuncsCorr but the PATTERN around it shows how arg sub-stepping works.

## TARGET 2: captured variable (LINE 3334)

```lean
| some idx =>
  -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
  sorry
```

**WARNING**: This is a multi-step gap. Core resolves variable in 1 step. Flat needs 2 steps (var lookup + getEnv). May need a 2-step simulation lemma.

## COLLISION AVOIDANCE
jsspec works on L6038. You work on L3334 and L4423.
Do NOT edit L6000+.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
