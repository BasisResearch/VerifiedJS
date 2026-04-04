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

## TASK 1 (DO THIS): Prove NoNestedAbrupt_step_preserved at L9180

L9176-9180 is:
```lean
private theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr) (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr := by
  sorry
```

### KEY INSIGHT: You need WELL-FOUNDED INDUCTION on `sf.expr.depth`, not just `cases`.

`Flat.step?` is defined by WF recursion on `s.expr.depth`. For context-stepping cases (e.g., `.seq a b` where `a` is non-value), it calls `step? { s with expr := a }` recursively, producing `sa` with `sa.expr.depth < a.depth ≤ (.seq a b).depth`. The output is `.seq sa.expr b`. To show `NoNestedAbrupt (.seq sa.expr b)`, you need the **IH**: `NoNestedAbrupt a → step? ... = some (..., sa) → NoNestedAbrupt sa.expr`.

### PROOF STRUCTURE:

```lean
  -- Destruct sf to get named fields
  obtain ⟨expr, env, heap, trace, funcs, cs⟩ := sf
  simp only [Flat.State.expr] at hna
  -- WF induction on expr depth
  induction expr using (Flat.Expr.recOn (motive := fun e => ...)) with  -- OR use:
  -- Alternative: strong induction on Nat
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
    ...
```

### CASE-BY-CASE ANALYSIS (from reading Flat.step? at Flat/Semantics.lean:336-1002):

**VACUOUSLY TRUE cases** (NoNestedAbrupt has no constructor for these — `cases hna` closes them immediately):
- `.unary`, `.binary`, `.while_`, `.labeled`, `.makeClosure`, `.getEnv`, `.makeEnv`, `.objectLit`, `.arrayLit`, `.tryCatch`
- Just do `cases hna` — Lean will close the goal since no constructor matches.

**SIMPLE cases** (step produces `.lit`):
- `.lit` → `simp [Flat.step?] at hstep` — contradiction (step? returns none)
- `.var name` → steps to `.lit v` → `exact NoNestedAbrupt.lit`
- `.this` → steps to `.lit v` → `exact NoNestedAbrupt.lit`
- `.break label` → steps to `.lit .undefined` → `exact NoNestedAbrupt.lit`
- `.continue label` → steps to `.lit .undefined` → `exact NoNestedAbrupt.lit`

**MEDIUM cases** (value sub-case produces value, non-value needs IH):
- `.seq a b`:
  - `cases hna with | seq ha hb => ...`
  - `simp [Flat.step?] at hstep`
  - Case split on `exprValue? a`:
    - `some v`: steps to `b` → `exact hb`
    - `none`: steps to `.seq sa.expr b` where `step? {expr := a, ...} = some (_, sa)`.
      Need: `NoNestedAbrupt sa.expr` from IH (a.depth < n), then `exact NoNestedAbrupt.seq (ih ... ha ...) hb`
- `.let name init body`: Same pattern. Value: steps to `body` → `exact hbody`. Non-value: `.let name init'.expr body` → IH on init.
- `.assign name rhs`: Value: `.lit v` → `NoNestedAbrupt.lit`. Non-value: `.assign name rhs'.expr` → IH.
- `.if cond then_ else_`: Value: steps to `then_` or `else_` → `exact hthen` or `exact helse`. Non-value: `.if cond'.expr then_ else_` → IH.
- `.throw arg`: Value: `.lit .undefined` → `NoNestedAbrupt.lit`. Non-value: `.throw arg'.expr` → need `hasAbruptCompletion arg'.expr = false`. But `hna` gives `hasAbruptCompletion arg = false`. **Problem**: does stepping preserve `hasAbruptCompletion = false`? You may need a helper lemma or `sorry` this sub-case.
- `.return arg`: `none` case: `.lit .undefined` → `NoNestedAbrupt.lit`. `some e`: value case: `.lit v` → `NoNestedAbrupt.lit`. Non-value: `.return (some e'.expr)` → same issue as throw with `hasAbruptCompletion`.
- `.await arg`: Value: `.lit v` → `NoNestedAbrupt.lit`. Non-value: `.await arg'.expr` → `hasAbruptCompletion` preservation needed.
- `.yield arg d`: `none`: `.lit .undefined` → `NoNestedAbrupt.lit`. `some e`: value → `.lit v` → lit. Non-value: `.yield (some e'.expr) d` → `hasAbruptCompletion` preservation.

**COMPLEX cases** (multiple sub-expressions, step order depends):
- `.call f env args`, `.newObj f env args`: Need IH for whichever sub-expression is being evaluated. The constructor `NoNestedAbrupt.call hf henv hargs` gives hypotheses for all sub-expressions. Use IH on the stepped sub-expression, reconstruct with the other hypotheses.
- `.getProp obj prop`, `.setProp`, `.getIndex`, `.setIndex`, `.deleteProp`, `.typeof`: Similar pattern — one or two sub-expressions, IH on the stepped one.

### STRATEGY: Start with vacuously-true + simple cases. Get them done first. Then medium cases one by one. For complex cases or `hasAbruptCompletion` preservation issues, use `sorry` and move on.

Even getting the easy ~20 cases done and leaving ~5 sorry sub-cases is HUGE progress.

### hasAbruptCompletion PRESERVATION HINT:
If you need it, write a helper:
```lean
private theorem hasAbruptCompletion_step_preserved (e : Flat.Expr) (env heap trace funcs cs ev sf')
    (hac : hasAbruptCompletion e = false)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf')) :
    hasAbruptCompletion sf'.expr = false := by
  sorry -- separate theorem, prove later
```
Use it to close the throw/return/await/yield sub-cases. -1 sorry (L9180) → maybe +1 sorry for this helper = net zero but better structure.

## TASK 2 (ONLY IF TASK 1 IS DONE): trivialChain_return_steps
Same as before — copy trivialChain_throw_steps pattern.

## DO NOT:
- Work on Group A (L7516-7702) — PARKED
- Work on L8850 (let), L8898 (while), L9063/9064/9129/9130 (if) — wasmspec handles
- Work on L8343 (compound throw dispatch) — DEFERRED
- Work on L9174 (tryCatch) — DEFERRED
- Work on L9571/L9624 (break/continue) — PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
