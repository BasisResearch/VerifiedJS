# proof — WEAKEN CALLSTACK INVARIANT + CLOSE IF-COND-STEP + COMPOUND THROW

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- BUILD PASSES. 0 errors.
- ANF: 48 sorries. CC: 15. Lower: 0.
- Error propagation DONE in Flat/Semantics.lean.
- Your last run (21:30) exited with code 1 before doing work.

## P0: WEAKEN 4 CALLSTACK INVARIANT SORRIES (L2983, L3004, L3025, L3046)

These 4 sorries are UNPROVABLE as stated. The invariant says:
```
s'.callStack = cs ∧ ((∃ e', s'.expr = .throw e') ∨ (∃ v, s'.expr = .lit v))
```

But after error propagation, when `t = .error msg`, `s'.expr = si.expr` (the inner stepped expression), which could be ANYTHING — not necessarily `.throw` or `.lit`.

**FIX**: Weaken the invariant to:
```lean
s'.callStack = cs ∧ ((∃ e', s'.expr = .throw e') ∨ (∃ v, s'.expr = .lit v) ∨ (∃ msg, t = .error msg))
```

Steps:
1. Change the conclusion of `step?_throw_callStack_inv` (L2960) to add `∨ (∃ msg, t = .error msg)`
2. The sorry at L2983 becomes: `exact ⟨rfl, .inr (.inr ⟨s✝, rfl⟩)⟩`
3. Do the same for `step?_return_some_callStack_inv` (L2988), `step?_await_callStack_inv` (L3009), `step?_yield_some_callStack_inv` (L3030)
4. **UPDATE ALL CALLERS** — search for uses of these 4 theorems. Each caller currently pattern-matches on `.inl ⟨e', he⟩ | .inr ⟨v, hv⟩`. Add a third branch `| .inr (.inr ⟨msg, hmsg⟩)` handling the error case.

Use `lean_local_search` to find callers. The error case in callers likely needs: the step produced `.error msg`, so the trace already has the error — match the ANF trace.

## P1: CLOSE Flat_step?_if_cond_step (L12524)

Goal at L12524:
```
⊢ Flat.step? { s with expr := .if cond then_ else_ } =
  some (t, { expr := .if sc.expr then_ else_, env := sc.env, ... })
```

With error propagation, Flat.step? on `.if cond then_ else_` where cond is not a value now has a match on the step result's event. Need to:
1. `unfold Flat.step? ; simp [hnv]`
2. Split on whether `t` is `.error _` or not
3. Non-error: the if wraps the result → matches conclusion
4. Error: Flat.step? propagates error, unwrapping .if → conclusion says `.if sc.expr then_ else_` but actual result is `sc.expr` without the wrapper. **IF this case is unprovable**, add `(hne : ∀ msg, t ≠ .error msg)` hypothesis to the theorem statement, and update callers to provide it.

Check the actual Flat.step? definition for `.if` with `lean_hover_info` first.

## P2: COMPOUND THROW CASES (L11784) — IF P0+P1 DONE

L11784 has ~25 HasThrowInHead constructor cases. Each needs multi-step Flat simulation showing the throw sub-expression evaluates and produces the error trace. With error propagation done, compound cases (seq, let, assign) should propagate errors. Needs IH on the sub-expression.

Lower priority — focus on P0 and P1 first.

## CONCURRENCY
- wasmspec works on labeled_branch (L10333-L10706) and Cat B break/continue
- jsspec works on ClosureConvertCorrect.lean only
- YOU own Flat/Semantics.lean and ANFConvertCorrect.lean (except wasmspec's labeled_branch area)

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — CALLSTACK WEAKENING + IF-COND-STEP" >> agents/proof/log.md`
2. P0: Weaken 4 callStack invariant theorems, fix callers
3. P1: Fix or guard Flat_step?_if_cond_step
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
