# jsspec — YOU MUST WORK ON functionDef (L6174) FIRST. NOTHING ELSE.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 actual sorries.

## ⚠️ YOU WASTED YOUR LAST 3 RUNS ON BLOCKED TARGETS ⚠️
You keep investigating tryCatch, call, if-then/false — ALL of these are BLOCKED by CCStateAgree.
STOP. DO NOT investigate ANY of these:
- tryCatch (L6328, L6357) — BLOCKED
- call (L4226) — BLOCKED (no FuncsCorr)
- if-then/false (L3648, L3671) — BLOCKED
- while_ (L6464) — BLOCKED
- getIndex string (L5014) — semantic mismatch, SKIP
- forIn/forOf (L1507/L1508) — UNPROVABLE stubs

## YOUR ONE AND ONLY TARGET: functionDef (LINE 6174)

```lean
| functionDef fname params body isAsync isGen => sorry
```

This is at LINE 6174 of ClosureConvertCorrect.lean. It is a LEAF case. No sub-expression stepping. No CCStateAgree issue. FRESH and UNEXPLORED.

### How to prove it:
1. Run `lean_goal` at line 6174, column 50 of ClosureConvertCorrect.lean
2. The Core side: `Core.step?` on `functionDef fname params body isAsync isGen` creates a closure and stores it
3. The Flat side: `Flat.convertExpr` of functionDef produces something — check with `lean_hover_info` on `Flat.convertExpr` or read lines around 6174 for the conversion
4. Show both sides create a closure/function value and store it, and that the results correspond
5. Use `lean_multi_attempt` to try tactics at that position

### If functionDef turns out to be blocked too:
ONLY THEN move to captured variable at L3320:
```lean
| some idx =>
  -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
  sorry
```

### COLLISION AVOIDANCE
wasmspec works on L5000-6053. You work on L3000-5000 and L6100+.
Do NOT edit L5000-6053.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at functionDef sorry (L6174)
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
