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

## STATUS: objectLit + arrayLit + tryCatch + getProp + setProp CLOSED! Only call remains.

CC has 13 real sorries total:
- **L3921 (1): Core_step_preserves_supported: call — PRIORITY 1**
- L4109 (1): captured variable (multi-step sim, staging sorry)
- L4438, L4461 (2): CCStateAgree if-branches (architecturally blocked)
- L5025 (1): funcs correspondence
- L5233, L5241 (2): semantic mismatch (architecturally blocked)
- L5879 (1): UNPROVABLE getIndex string (SKIP)
- L7121 (1): functionDef
- L7278, L7279 (2): tryCatch CCStateAgree (architecturally blocked)
- L7351 (1): tryCatch inner
- L7459 (1): while_ CCState threading (architecturally blocked)

## TASK 1: Close L3921 (call) — HIGHEST PRIORITY

The call case at L3921 needs a FuncsSupported invariant. The approach:

1. Add to `Core_step_preserves_supported` signature:
```lean
(hfuncs : ∀ (i : Nat) (c : Core.Closure), s.funcs[i]? = some c → c.body.supported = true)
```

2. In the call case: when callee and args are all values and it's a function call:
   - The step produces `.tryCatch funcDef.body "__call_frame_return__" ...`
   - funcDef.body.supported comes from `hfuncs`
   - Thread hfuncs through the IH (since step? preserves funcs)

3. **After adding hfuncs**: update the `hsupp'` derivation to also derive `hfuncs'` from `hfuncs` (since Core.step? preserves funcs).

4. Update all callers of Core_step_preserves_supported to pass `hfuncs`.

**WARNING**: Adding a parameter to Core_step_preserves_supported will break all call sites. Track and fix them.

## TASK 2: Close L4109 (captured variable) — MEDIUM PRIORITY

At L4109: captured variable case in closureConvert_step_simulation. Multi-step sim needed.

## TASK 3: Close L7121 (functionDef) — IF TIME

## PRIORITY ORDER
1. L3921 (call) — last Core_step_preserves_supported case
2. L4109 (captured variable)
3. L7121 (functionDef)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
