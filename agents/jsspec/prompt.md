# jsspec — Close remaining Core_step_preserves_supported cases + CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: getIndex + setIndex CLOSED! Great. 4 cases remain in Core_step_preserves_supported.

CC has 16 real sorries total:
- L3914-3917 (4): Core_step_preserves_supported: call, objectLit, arrayLit, tryCatch
- L3983 (1): captured variable (multi-step sim)
- L4312, L4335 (2): CCStateAgree if-branches (architecturally blocked)
- L4899 (1): funcs correspondence
- L5107, L5115 (2): semantic mismatch (architecturally blocked)
- L5753 (1): UNPROVABLE getIndex string
- L6995 (1): functionDef
- L7152, L7153 (2): tryCatch CCStateAgree (architecturally blocked)
- L7225 (1): tryCatch inner
- L7333 (1): while_ CCState threading (architecturally blocked)

## TASK 1: Close L3914 (call) — HIGHEST PRIORITY

The call case needs a FuncsSupported invariant. Add to Core_step_preserves_supported signature:
```lean
(hfuncs : ∀ (i : Nat) (c : Core.Closure), s.funcs[i]? = some c → c.body.supported = true)
```

Then in the call case when callee and args are all values and it's a function call:
- The step produces `.tryCatch funcDef.body "__call_frame_return__" ...`
- funcDef.body.supported comes from `hfuncs`
- Thread hfuncs through the IH calls (step? preserves funcs)

**IMPORTANT**: After adding hfuncs, update the `hsupp'` derivation at L3956 to also derive `hfuncs'` from `hfuncs` (since Core.step? preserves funcs).

## TASK 2: Close L3915/L3916 (objectLit/arrayLit)

These need list induction via firstNonValue helpers.

Pattern for objectLit:
```lean
| objectLit =>
  -- split on firstNonValueProp props
  cases hfnv : Core.firstNonValueProp props with
  | none =>
    -- all values: step? produces .lit (.object addr)
    simp [Core.step?, Core.exprValue?, Core.firstNonValueProp, hfnv, Core.pushTrace] at hstep
    obtain ⟨-, rfl⟩ := hstep; rfl
  | some ⟨pre, name, target, post⟩ =>
    -- stepping target in the prop list
    cases h_sub : Core.step? { s with expr := target } with
    | none => simp [Core.step?, hfnv, h_sub] at hstep
    | some p =>
      obtain ⟨t, sa⟩ := p
      -- forward lemma for objectLit stepping
      -- reconstruct: result is objectLit (pre ++ [(name, sa.expr)] ++ post)
      -- use IH on target, then propListSupported_append
      sorry -- fill in with exact tactic sequence
```

Use `lean_local_search` for helper lemma names like `propListSupported_append`, `Core.step_objectLit_step_prop`.

## TASK 3: Close L3917 (tryCatch)

Pattern: case split on body value/error. In each branch, show supported is preserved.

## TASK 4: Close L3983 (captured variable) — IF TIME

This is `| some idx =>` in the var case. Flat produces `.getEnv (.var envVar) idx` which takes 2 steps (var lookup + getEnv), while Core takes 1 step. This needs a multi-step simulation or a different approach.

## PRIORITY ORDER
1. L3914 (call) — with FuncsSupported invariant
2. L3915 (objectLit) — list induction
3. L3916 (arrayLit) — same pattern as objectLit
4. L3917 (tryCatch) — case split
5. L3983 (captured variable) — if time

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
