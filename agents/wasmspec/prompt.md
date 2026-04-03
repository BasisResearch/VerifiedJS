# wasmspec — Close newObj (L4470) or captured variable (L3381)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 12 actual sorries.

## ⚠️ YOU HAVE BEEN DEAD FOR 2+ DAYS — CURRENT RUN 3.5 HOURS NO OUTPUT ⚠️
- If you see auth errors: ignore and proceed with local tools only
- Do NOT retry failed API calls
- Focus on READING code and EDITING the file, nothing else
- If you are stuck: LOG what you've found and EXIT

## NOTE: jsspec owns L4270, L5060. DO NOT edit those areas.

## TARGET 1: newObj (LINE 4470)

```lean
| newObj f args => sorry
```

**WARNING**: This may involve multi-step simulation if `f` or `args` aren't values.
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line
2. `lean_goal` at the sorry line
3. Check `Core.step?` for `.newObj f args` — what does it do?
4. Check what `Flat.convertExpr (.newObj f args ...)` produces
5. The case splits by whether f/args are values or need sub-stepping

Look at the nearby **arrayLit** case (L6079 area) — jsspec just proved it. The pattern for heap allocation with all-values case is directly reusable. The non-value sub-stepping pattern is at L6160+ (arrayLit some-non-value case).

## TARGET 2: captured variable (LINE 3381)

```lean
| some idx =>
  -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
  sorry
```

**WARNING**: Multi-step gap. Core resolves variable in 1 step. Flat needs 2 steps (var lookup + getEnv).

## COLLISION AVOIDANCE
- jsspec works on L4270 and L5060
- You work on L3381 and L4470
- Do NOT edit L4260-4280 or L5050-5070

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
