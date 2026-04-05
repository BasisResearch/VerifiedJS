# jsspec — Close remaining 8 Core_step_preserves_supported + CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: GREAT WORK! You closed 10 sorries last run (18→8 in Core_step_preserves_supported).

The depth induction + suffices + Nat.strongRecOn approach WORKS. You proved return, let, assign, if, seq, throw, typeof, unary, binary, deleteProp. 8 remaining.

## TASK 1: Close remaining 8 in Core_step_preserves_supported (L3675-3682)

Remaining cases:
```lean
| getProp => sorry
| setProp => sorry
| getIndex => sorry
| setIndex => sorry
| call => sorry
| objectLit => sorry
| arrayLit => sorry
| tryCatch => sorry
```

### getProp (L3675)
Pattern: `getProp obj prop`. If obj is a value, Core.step? does heap lookup → result is a value (lit) → supported by rfl. If obj is not a value, step steps obj → IH on obj.depth.
```lean
| getProp obj prop =>
  cases hval : Core.exprValue? obj with
  | some v =>
    -- obj is a value, step? does heap lookup, result is .lit something
    simp [Core.step?, hval] at hstep
    split at hstep <;> simp_all [Core.pushTrace, Core.Expr.supported]
  | none =>
    -- obj not a value, step? steps obj
    cases h_sub : Core.step? { s with expr := obj } with
    | none => simp [Core.step?, hval, h_sub] at hstep
    | some p =>
      obtain ⟨t, sa⟩ := p
      have hfwd := Core.step_getProp_step_obj obj prop s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
      rw [hfwd] at hstep
      simp only [Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      simp only [Core.pushTrace, Core.Expr.supported]
      exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
        { s with expr := obj } sa t (Nat.le_refl _) hsupp h_sub
```

Check if `Core.step_getProp_step_obj` exists with `lean_local_search`. If not, you need to write a forward lemma first.

### setProp (L3676)
Similar 3-level pattern: obj not value → step obj; obj value, val not value → step val; both values → heap write → .lit result.

### getIndex / setIndex (L3677-3678)
Same pattern as getProp/setProp but with index expressions.

### call (L3679)
More complex: has func expr, optional env, args list. When func not value → step func. When func value but env not value → step env. When both value but args has non-value → step first non-value arg. When all values → call invocation.

Use `lean_goal` to see the exact state. The key is `Core.firstNonValue` for the args list. You may need separate lemmas or `List.induction`.

### objectLit / arrayLit (L3680-3681)
These use `firstNonValue` on a list of expressions. Pattern:
- If all values: step? allocates on heap → .lit (.object addr) → supported
- If has non-value: step? steps it → IH on depth

You may need induction on the list or a `firstNonValue_depth_lt` lemma.

### tryCatch (L3682)
`tryCatch body catch_ finally_`. If body not value → step body. If body is error → catch path. If body is value → result.

### Strategy
- Do getProp first — it's closest to deleteProp which you already proved
- setProp/getIndex/setIndex follow the same pattern
- Use `lean_multi_attempt` to test tactic sequences before editing
- For each case, check if the relevant `Core.step_X_step_Y` forward lemma exists

## TASK 2: Other CC sorries (IF TIME after Task 1)

After Core_step_preserves_supported is fully proved, these remain:
- L3748: captured variable simulation (2-step Flat)
- L4077, L4100: if CCStateAgree
- L4664: non-consoleLog function call
- L4872, L4880: non-value func/arg semantic mismatch
- L5518: getIndex string (marked UNPROVABLE — consider removing or axiomatizing)
- L6760: functionDef
- L6917, L6918, L6990, L7098: tryCatch/while CCState threading

For L4077/L4100, use `lean_goal` to see what's needed — these are often fixable by choosing the right witness state.

## PRIORITY ORDER
1. getProp, setProp (closest to proven deleteProp pattern)
2. getIndex, setIndex (same pattern)
3. call (harder, needs args list handling)
4. objectLit, arrayLit (needs list induction)
5. tryCatch (needs error path analysis)
6. Other CC sorries if time

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
