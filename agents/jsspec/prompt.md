# jsspec — Close call case in Core_step_preserves_supported + remaining CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: Running 2.5h on call case. Check your actual progress.

CC has 13 real sorries total:
- **L3921 (1): Core_step_preserves_supported: call — PRIORITY 1**
- L4107 (1): captured variable (multi-step sim, staging sorry)
- L4436, L4459 (2): CCStateAgree if-branches (architecturally blocked)
- L5023 (1): funcs correspondence
- L5231, L5239 (2): semantic mismatch (architecturally blocked)
- L5877 (1): UNPROVABLE getIndex string (SKIP)
- L7119 (1): functionDef
- L7276, L7277 (2): tryCatch CCStateAgree (architecturally blocked)
- L7349 (1): tryCatch inner
- L7457 (1): while_ CCState threading (architecturally blocked)

## TASK 1: Close L3921 (call) — HIGHEST PRIORITY

**If you have NOT yet added hfuncs parameter**: The approach is:
1. Add `(hfuncs : ∀ (i : Nat) (c : Core.Closure), s.funcs[i]? = some c → c.body.supported = true)` to `Core_step_preserves_supported`
2. In the call case: use hfuncs to get closure.body.supported
3. Update all callers to pass hfuncs

**If you HAVE added hfuncs but it broke callers**: Fix the callers first. Use `lean_diagnostic_messages` to find errors.

**If you're stuck on Core.step? expansion for call**: The call case in Core.step? is complex (firstNonValue, function lookup, etc.). Use `lean_goal` at L3921 to see exact state. Try `unfold Core.step? at hstep` then case-split on `Core.firstNonValue`.

**ALTERNATIVE simpler approach if stuck**: Instead of modifying the theorem signature, try:
```lean
| call => sorry -- leave for now, work on L7119 (functionDef) instead
```
L7119 (functionDef) might be easier — it's a standalone case.

## TASK 2: Close L7119 (functionDef) — MEDIUM PRIORITY

This is `closureConvert_step_simulation` case for `functionDef`. Check with `lean_goal` at L7119.

## PRIORITY ORDER
1. L3921 (call) — if stuck after 30min, move to L7119
2. L7119 (functionDef)
3. L4107 (captured variable)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
