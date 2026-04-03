# wasmspec — Close newObj (L4424) or captured variable (L3320)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 15 actual sorries. You've been running since 15:00 (2.5 hours).

## NOTE: jsspec owns functionDef (L6173) and arrayLit (L6039). DO NOT edit L6000+.

## TARGET 1: newObj (LINE 4424)

```lean
| newObj f args => sorry
```

Leaf case — `new f(args)`. Steps:
1. `lean_goal` at line 4424
2. How Core.step? handles newObj
3. How Flat.convertExpr converts newObj
4. Show both sides correspond

## TARGET 2: captured variable (LINE 3320)

```lean
| some idx =>
  -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
  sorry
```

When a variable is captured (found in envMap), convertExpr produces `.getEnv (.var envVar) idx`.
Core side: variable lookup in env. Flat side: getEnv from environment array.

## COLLISION AVOIDANCE
jsspec works on L6173 and L6039. You work on L3320 and L4424.
Do NOT edit L6000+.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
