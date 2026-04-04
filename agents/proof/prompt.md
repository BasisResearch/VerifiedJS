# proof — Close L9180 (NoNestedAbrupt_step_preserved) via WF induction

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## STATE: ANF has 24 sorry lines. L9180 (NoNestedAbrupt_step_preserved) is your ONE target.

## TASK 1 (DO THIS NOW): Prove NoNestedAbrupt_step_preserved at L9180

L9176-9180 is:
```lean
private theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr) (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr := by
  sorry
```

### APPROACH: Strong Nat induction on expr.depth

```lean
  obtain ⟨expr, env, heap, trace, funcs, cs⟩ := sf
  simp only [Flat.State.expr] at hna
  suffices ∀ n e, e.depth ≤ n → ∀ env heap trace funcs cs ev sf',
    NoNestedAbrupt e →
    Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf') →
    NoNestedAbrupt sf'.expr from this _ _ (le_refl _) _ _ _ _ _ hna hstep
  intro n
  induction n with
  | zero => intro e hd; cases e <;> simp [Flat.Expr.depth] at hd <;> omega
  | succ n ih =>
    intro e hd env heap trace funcs cs ev sf' hna hstep
    cases e with
    | lit v => simp [Flat.step?] at hstep
    | var name => simp [Flat.step?] at hstep; split at hstep <;> simp_all; exact NoNestedAbrupt.lit
    | this => simp [Flat.step?] at hstep; simp_all; exact NoNestedAbrupt.lit
    | break label => simp [Flat.step?] at hstep; simp_all; exact NoNestedAbrupt.lit
    | continue label => simp [Flat.step?] at hstep; simp_all; exact NoNestedAbrupt.lit
    -- VACUOUSLY TRUE: NoNestedAbrupt has no constructor → `cases hna` closes
    | unary op e => cases hna
    | binary op l r => cases hna
    | while_ cond body => cases hna
    | labeled label body => cases hna
    | makeClosure params body isAsync isGen => cases hna
    | getEnv => cases hna
    | makeEnv bindings => cases hna
    | objectLit props => cases hna
    | arrayLit elems => cases hna
    | tryCatch body catchVar catchBody finally_ => cases hna
    -- MEDIUM: seq, let, assign, if
    | seq a b =>
      cases hna with | seq ha hb =>
      simp [Flat.step?] at hstep
      -- case split on exprValue? a
      sorry -- USE: if value → exact hb; if non-value → IH on a (depth a < depth .seq)
    | «let» name init body =>
      sorry
    | assign name rhs =>
      sorry
    | «if» cond then_ else_ =>
      sorry
    -- THROW/RETURN/AWAIT/YIELD: value → lit, non-value → IH + hasAbruptCompletion preservation
    | throw arg =>
      sorry
    | «return» arg =>
      sorry
    | await arg =>
      sorry
    | yield arg d =>
      sorry
    -- COMPLEX: call, newObj, prop access, etc.
    | call f fenv args => sorry
    | newObj f fenv args => sorry
    | getProp obj prop => sorry
    | setProp obj prop val => sorry
    | getIndex obj idx => sorry
    | setIndex obj idx val => sorry
    | deleteProp obj prop => sorry
    | typeof e => sorry
```

### STRATEGY: CLOSE AS MANY CASES AS YOU CAN. Even 10 sub-case sorries is better than 1 monolithic sorry.

1. **Vacuously true** (10 cases): `cases hna` closes instantly. DO THESE FIRST.
2. **Simple** (5 cases): lit/var/this/break/continue. `simp [Flat.step?]` then `exact NoNestedAbrupt.lit`.
3. **seq**: The most important medium case. `exprValue? a` split. Value → `exact hb`. Non-value → IH via `ih _ a (by simp [Flat.Expr.depth]; omega) ... ha ...`.
4. **Others**: Use `sorry` for any sub-case that takes >10 min.

### hasAbruptCompletion preservation helper
For throw/return/await/yield, write this FIRST:
```lean
private theorem hasAbruptCompletion_step_preserved (e : Flat.Expr) (env heap trace funcs cs ev sf')
    (hac : hasAbruptCompletion e = false)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf')) :
    hasAbruptCompletion sf'.expr = false := by
  sorry -- separate theorem, prove later
```
Use it to close the throw/return/await/yield non-value sub-cases.

## TASK 2 (ONLY IF TASK 1 IS DONE): trivialChain_return_steps
Copy trivialChain_throw_steps pattern for return.

## DO NOT:
- Work on Group A (L7516-7702) — PARKED
- Work on L8850 (let), L8898 (while), L9063/9064/9129/9130 (if) — wasmspec handles
- Work on L8343 (compound throw dispatch) — DEFERRED
- Work on L9174 (tryCatch) — DEFERRED
- Work on L9571/L9624 (break/continue) — PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
