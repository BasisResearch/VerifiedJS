# jsspec — Close call case in Core_step_preserves_supported + remaining CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: objectLit + arrayLit + tryCatch CLOSED! GREAT WORK! Only call remains in Core_step_preserves_supported.

CC has 13 real sorries total:
- L3914 (1): Core_step_preserves_supported: **call** — PRIORITY 1
- L4082 (1): captured variable (multi-step sim, staging sorry)
- L4411, L4434 (2): CCStateAgree if-branches (architecturally blocked)
- L4998 (1): funcs correspondence
- L5206, L5214 (2): semantic mismatch (architecturally blocked)
- L5852 (1): UNPROVABLE getIndex string (SKIP)
- L7094 (1): functionDef
- L7251, L7252 (2): tryCatch CCStateAgree (architecturally blocked)
- L7324 (1): tryCatch inner
- L7432 (1): while_ CCState threading (architecturally blocked)

## TASK 1: Close L3914 (call) — HIGHEST PRIORITY

The call case needs a FuncsSupported invariant. Add to Core_step_preserves_supported signature:
```lean
(hfuncs : ∀ (i : Nat) (c : Core.Closure), s.funcs[i]? = some c → c.body.supported = true)
```

Then in the call case when callee and args are all values and it's a function call:
- The step produces `.tryCatch funcDef.body "__call_frame_return__" ...`
- funcDef.body.supported comes from `hfuncs`
- Thread hfuncs through the IH calls (step? preserves funcs)

**IMPORTANT**: After adding hfuncs, update the `hsupp'` derivation to also derive `hfuncs'` from `hfuncs` (since Core.step? preserves funcs).

## TASK 2: Close L4082 (captured variable) — MEDIUM PRIORITY

At L4082: captured variable case in closureConvert_step_simulation. Flat produces `.getEnv (.var envVar) idx` which takes 2 steps (var lookup + getEnv), while Core takes 1 step (var lookup). This needs a multi-step simulation: show Flat.Steps sf [.silent, ev] sf' where first step resolves var, second does getEnv.

Use `lean_goal` at L4082 to see the proof state. Pattern:
```lean
-- Flat: .getEnv (.var envVar) idx
-- Step 1: var envVar → .lit envValue (from env lookup)
-- Step 2: getEnv (.lit envValue) idx → .lit capturedValue
refine ⟨sf', [.silent, ev], .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)), ?_, ?_, ?_⟩
```

## TASK 3: Close L7094 (functionDef) — IF TIME

Pattern: functionDef case in closureConvert_step_simulation. Core creates a closure and steps to `.lit closureAddr`. Flat does the same but with the converted body. Show CCStateAgree is maintained.

## PRIORITY ORDER
1. L3914 (call) — last Core_step_preserves_supported case
2. L4082 (captured variable) — multi-step sim
3. L7094 (functionDef) — if time

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
