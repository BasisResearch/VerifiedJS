# jsspec — PIVOT: Close easy CC sorries FIRST, then depth induction

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: Depth induction has been stuck for 3+ runs. PIVOTING to easier wins.

The depth induction on Core_step_preserves_supported (L3675-3682) is important but you've been stuck on it. Instead, close OTHER CC sorries first for concrete progress, then return to depth induction.

## TASK 1: CCStateAgree sorries (L4077, L4100, L6917, L6918, L6990) — EASIEST

These all say "CCStateAgree" — the CCState (nextId, funcs list) after converting one branch may differ from the state expected by the proof. Look at what CCStateAgree requires:

At L4077 (if-true branch):
```lean
sorry⟩ -- CCStateAgree st' vs then_-only state: needs different st_a choice
```

The pattern is: `refine ⟨st_a, st_a', ..., ⟨rfl, rfl⟩, sorry⟩` where the sorry needs to show the output CCState matches. The fix is usually to pick the RIGHT `st_a` and `st_a'` in the `refine`.

**Approach**: Use `lean_goal` at each sorry to see EXACTLY what's needed. Often the fix is:
- Change which CCState you pick as `st_a`/`st_a'`
- Use `CCState_agree_trans` or similar lemma
- Or prove `convertExpr_snd_monotone` (conversion only increments nextId)

Try each one. If the goal is just `st_a = st_b` for specific states, trace back through the convertExpr calls to find the right choice.

## TASK 2: L3748 (captured variable sorry)

This is the `var` case where `lookupEnv envMap name = some idx`:
```lean
| some idx =>
  simp [hlookupEnv] at hconv
  sorry
```

The converted expression is `.getEnv (.var envVar) idx`. When Flat steps this:
1. First step: evaluate `.var envVar` → looks up envVar in env
2. Second step: `.getEnv (.lit envObj) idx` → indexes into the environment object

This is a 2-step Flat reduction vs 1-step Core (var lookup). You need to show the simulation: Core looks up `name` in env, Flat does getEnv on the closure environment.

Use `lean_goal` at L3748 to see the exact proof state. The key hypothesis should be `EnvCorrInj` which relates Core env to Flat env through the injMap.

## TASK 3: L4664 (non-consoleLog function call)

```lean
sorry -- non-consoleLog function call: needs sf.funcs[idx] ↔ sc.funcs[idx] correspondence
```

This needs a `FuncsCorr` invariant or similar. Check if CC_SimRel already has a funcs correspondence hypothesis. Use `lean_hover_info` on `CC_SimRel` to see its fields.

## TASK 4: L6760 (functionDef)

```lean
| functionDef fname params body isAsync isGen => sorry
```

This is the function definition case. Core creates a closure and stores it. Flat's convertExpr for functionDef should produce a similar structure. Use `lean_hover_info` on `Flat.convertExpr` for the functionDef case.

## TASK 5: Depth induction (L3675-3682) — ONLY IF TASKS 1-4 DONE

If you finish the above, return to the depth induction approach from the previous prompt. The `suffices` wrapper with induction on `Core.Expr.depth` is the right strategy.

## PRIORITY ORDER
1. L4077, L4100 (if CCStateAgree) — likely quick fixes
2. L6917, L6918, L6990 (tryCatch CCStateAgree) — same pattern
3. L3748 (captured var)
4. L4664 (function call FuncsCorr)
5. L6760 (functionDef)
6. Depth induction (L3675-3682)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
