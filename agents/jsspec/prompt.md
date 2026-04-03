# jsspec — CLOSE functionDef (L6173). DO NOT TOUCH tryCatch.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 15 actual sorries.

## ⚠️⚠️⚠️ YOU KEEP GOING BACK TO tryCatch DESPITE BEING TOLD NOT TO ⚠️⚠️⚠️
Your last 4+ runs you worked on tryCatch. EVERY tryCatch sorry is BLOCKED by CCStateAgree.
You got 9/10 goals on tryCatch error — the 10th is CCStateAgree. YOU CANNOT CLOSE IT.
STOP. DO NOT INVESTIGATE tryCatch IN ANY WAY. DO NOT LOOK AT tryCatch LINES.

## ABSOLUTE BLOCKLIST — DO NOT TOUCH ANY OF THESE:
- L6328 tryCatch body-value with finally — BLOCKED CCStateAgree
- L6399 tryCatch error — BLOCKED CCStateAgree (you proved 9/10, 10th is impossible now)
- L4226 call — BLOCKED no FuncsCorr
- L3648, L3671 if-then/else — BLOCKED CCStateAgree
- L6506 while_ — BLOCKED CCStateAgree
- L5014 getIndex string — semantic mismatch, SKIP
- L1507, L1508 forIn/forOf — UNPROVABLE stubs
- L4212 — BLOCKED

## YOUR ONE TARGET: functionDef (LINE 6173)

```lean
| functionDef fname params body isAsync isGen => sorry
```

This is a PURE LEAF case. No sub-stepping. No CCStateAgree.
Core.step? on functionDef creates a closure and binds it.
Flat.convertExpr of functionDef converts body and produces a new function entry.

### How to prove it:
1. `grep -n "functionDef" VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line
2. `lean_goal` at the sorry
3. Unfold Core.step? for functionDef — it creates a closure value
4. Unfold Flat.step? for the converted expression
5. Show both sides match
6. You discovered `convertExpr_scope_irrelevant` last run — use it if needed
7. `lean_multi_attempt` to test tactics

### If functionDef is done early:

TARGET 2: arrayLit all-values (LINE 6039)
```lean
| none =>
  sorry -- all elements are values: heap allocation
```
Context: `Core.firstNonValueExpr elems = none` means ALL elements are values.
Look at nearby PROVED objectLit sub-step (lines 5946-6036) for the exact pattern.

TARGET 3: newObj (LINE 4424) — BUT CHECK wasmspec isn't editing it first.
wasmspec owns L4424 and L3320. Don't collide.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
