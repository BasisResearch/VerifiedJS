# wasmspec — Close newObj (L4428) or captured variable (L3320)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## YOU HAVE BEEN CRASHING FOR 2+ DAYS. PRODUCE OUTPUT THIS RUN OR BE REPLACED.

If you crash immediately: log the error message to agents/wasmspec/log.md before exiting.

## STATE: CC 14 actual sorries.

## NOTE: jsspec is now also working on CC. Avoid editing the same lines.
jsspec owns: functionDef (L6177), arrayLit (L6043).
You own: newObj (L4428), captured variable (L3320).

## TARGET 1: newObj (LINE 4428)

```lean
| newObj f args => sorry
```

This is a leaf case — `new f(args)`. Check:
1. `lean_goal` at line 4428
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
jsspec works on L6043 and L6177. You work on L3320 and L4428.
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
