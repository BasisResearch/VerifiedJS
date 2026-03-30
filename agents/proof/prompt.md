# proof — Close ANF expression cases + non-first-position context cases

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (15:30 Mar 30)
- ANF: 41 sorry instances across 3 groups:
  - 7 depth-induction sorries (L3825, 3829, 3840, 3891, 3895, 3906, 3923) — skip for now
  - 26 non-first-position context sorries (L4112-4124 + L4331-4343) — BLOCKED on Fix D
  - 8 expression-case sorries (L4439, 4441, 4443, 4463, 4465, 4467, 4469, 4471) — YOUR TARGET
- CC permissions FIXED ✓ (group writable)
- wasmspec applied hnoerr guards to CC ✓
- jsspec is about to apply Fix D to Flat/Semantics.lean (will unblock 26 context cases)

## PRIORITY 1: Close throw case (L4452-4463)

Your own analysis identified the right approach. The throw case at L4452 already has:
```lean
  | throw arg =>
    cases sa with | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    cases heval : ANF.evalTrivial sa_env arg <;> simp [heval] at hstep_eq
    all_goals obtain ⟨rfl, rfl⟩ := hstep_eq
    all_goals sorry
```

You need `hasThrowInHead_flat_value_steps` or equivalent. Build it:
1. `lean_goal` at L4463 to see exact goal state
2. The normalizeExpr of `.throw arg` produces an expr with throw in head
3. Flat steps: evaluate the trivial arg (0-1 steps), then throw produces error event
4. Use `lean_multi_attempt` at L4463 with candidate closings

If this is too hard, try return/yield/await first (L4467-4471) — same pattern but simpler.

## PRIORITY 2: Close let/seq/if (L4439-4443)

These are structurally simpler:
- **let** (L4439): rhs is either value (extend env, continue with body via IH) or non-value (step inner rhs). Use `lean_goal` to see what's available.
- **seq** (L4441): Same pattern. If `a` is value, skip to `b`. If not, step `a`.
- **if** (L4443): After ANF, cond is trivial. Evaluate, branch to then/else.

For each: `lean_goal` first, then `lean_multi_attempt` with tactics.

## PRIORITY 3: tryCatch (L4465) — hardest, do last

## DO NOT TOUCH:
- Non-first-position context cases (L4112-4124, L4331-4343) — these need Fix D first
- Depth-induction cases (L3825-3923) — lower priority
- ClosureConvertCorrect.lean — wasmspec owns this now

## VERIFICATION
- [ ] Build passes: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- [ ] At least 2 expression-case sorries closed this run
- [ ] Log to agents/proof/log.md with sorry count before/after
