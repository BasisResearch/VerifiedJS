# proof — BUILD AWAIT/YIELD SIM + DEPTH INDUCTION INFRASTRUCTURE

## CURRENT STATE: 17 ANF sorries. Target: ≤15 this run (-2).

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## CRITICAL FINDINGS FROM LAST RUN
1. **Exfalso approach on wildcards L1597/L1663/L1680 DOES NOT WORK.** Compound sub-expressions CAN produce `.labeled` through recursion. STOP trying exfalso on these.
2. **4 sorries are PERMANENT semantic mismatches**: throw (L1784), return (L1788), break (L1816), continue (L1818). ANF events don't match Flat events. These need semantics-level fixes, NOT proof fixes. SKIP them.
3. **Await (L1792) and yield (L1790) are FEASIBLE** — both produce `.silent` events in both ANF and Flat.

## PRIORITY 0: `normalizeExpr_await_step_sim` (-1 sorry at L1792)

Write a new theorem following the EXACT pattern of `normalizeExpr_var_step_sim` (L1326-1450). That theorem handles `normalizeExpr e k` producing `.trivial (.var name)`. You need the analogous one for `.await arg`.

**Theorem statement** (place above L1760):
```lean
private theorem normalizeExpr_await_step_sim :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat) (arg : ANF.Trivial),
    (∀ (t : ANF.Trivial) (n' : Nat), ∃ m', (k t).run n' = .ok (.trivial t, m')) →
    (ANF.normalizeExpr e k).run n = .ok (.await arg, m) →
    ∀ (sf : Flat.State), sf.expr = e →
    ExprWellFormed e sf.env →
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps sf evs sf' ∧
      -- After Flat steps, sf' matches ANF's post-await state
      ANF.evalTrivial sf.env arg = ANF.evalTrivial sf'.env arg ∧
      sf'.heap = sf.heap ∧
      observableTrace sf'.trace = observableTrace sf.trace ∧
      observableTrace evs = [] ∧
      -- sf' is positioned at .await (trivialToFlat arg) or similar
      (∃ flat_arg, sf'.expr = .await flat_arg ∧ Flat.exprValue? flat_arg ≠ none)
```

**Key structural insight**: `normalizeExpr (.await flat_arg) k = normalizeExpr flat_arg (fun t => pure (.await t))`. The `.await` constructor ignores `k` entirely. So:

- **Direct case**: `e = .await flat_arg`. Then normalizeExpr recurses into flat_arg with continuation `fun t => pure (.await t)`. Since result is `.await arg`, flat_arg normalized to trivial `arg`. Use `normalizeExpr_var_step_sim` (or adapt its proof) to show flat_arg evaluates to a value in Flat. Then `.await (lit v)` fires with `.silent`.
- **Seq case**: `e = .seq a b`. Consume trivial chain `a` via `trivialChain_consume_ctx`, recurse on `b` with IH.
- **Everything else**: exfalso. `.await` is NOT produced by `k` (k produces trivials). Use `normalizeExpr_compound_not_trivial` analog — you'll need a lemma showing these forms can't produce `.await`.

Look at L1448 for how the var_step_sim handles the "everything else" case: `normalizeExpr_compound_not_trivial`. You need `normalizeExpr_compound_not_await` or similar.

After this theorem is proved, L1792 becomes:
```lean
  | await arg =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    -- use normalizeExpr_await_step_sim to get Flat steps
    -- then match ANF.evalTrivial cases with Flat.step? on .await
    sorry -- fill after infrastructure
```

## PRIORITY 1: `normalizeExpr_yield_step_sim` (-1 sorry at L1790)

Same pattern as await. `normalizeExpr (.yield (some v) d) k = normalizeExpr v (fun t => pure (.yield (some t) d))`. The `.yield none d` case is trivial (no sub-expression).

## PRIORITY 2: Wildcard cases — DO NOT use exfalso

L1597, L1663, L1680 need induction on expression depth, NOT exfalso. The correct approach is restructuring `normalizeExpr_labeled_step_sim` (L1456) to be inductive. This is ~300 lines. Only attempt if P0+P1 are done.

## SKIP
- L1760 (let), L1762 (seq), L1764 (if) — hardest, need eval context lemmas
- L1784 (throw), L1788 (return), L1816 (break), L1818 (continue) — PERMANENT semantic mismatches
- L1786 (tryCatch) — hard

## WORKFLOW
1. Write `normalizeExpr_await_step_sim` → build → check errors
2. Use it to close L1792 → build
3. Write `normalizeExpr_yield_step_sim` → close L1790 → build
4. Log progress to agents/proof/log.md
