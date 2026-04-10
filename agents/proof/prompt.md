# proof — CLOSE CALLSTACK INVARIANT + COMPOUND SORRIES (ERROR PROP DONE)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- **ERROR PROPAGATION: DONE** — 48 `.error _` patterns in Flat/Semantics.lean. GREAT WORK.
- Flat/Semantics.lean: 0 sorries, 0 errors.
- ANF: ~44 sorries. Build passes.
- Your job now: CLOSE sorries that error propagation unblocked.

## P0: CLOSE CALLSTACK INVARIANT SORRIES (L2983, L3004, L3025, L3046)

These 4 sorries are in `step?_throw_callStack_inv`, `step?_return_some_callStack_inv`, `step?_await_callStack_inv`, `step?_yield_some_callStack_inv`.

Each has the goal pattern:
```
obtain ⟨-, rfl⟩ := hstep; exact ⟨rfl, sorry⟩  -- error propagation unwraps .throw
```

The error branch gives `s'.expr = sa.expr` (the inner sub-expression, unwrapped). The invariant says `s'.expr` is either still a `.throw e'` (or `.return`/`.await`/`.yield`) OR is `.lit v`.

After error propagation, in the `.error _` branch:
- `s'.expr = sa.expr` where `sa` is the result of stepping the inner expression
- The inner expression was being evaluated (not a value), so `sa.expr` could be anything
- The disjunction `(∃ e', s'.expr = .throw e') ∨ (∃ v, s'.expr = .lit v)` may NOT hold

**IF the invariant is too strong after error propagation**, weaken it:
```lean
s'.callStack = cs ∧ ((∃ e', s'.expr = .throw e') ∨ (∃ v, s'.expr = .lit v) ∨ (∃ msg, t = .error msg))
```
Then update callers to handle the new `.error` case.

**Check with `lean_goal` first** to see exactly what's needed.

## P1: CLOSE COMPOUND THROW/RETURN/AWAIT/YIELD SORRIES

These are the big wins from error propagation:
- **L11784**: `normalizeExpr_throw_step_sim` — main sorry
- **L11935, L11941**: compound inner_val + HasReturnInHead
- **L12112, L12118**: compound inner_arg + HasAwaitInHead
- **L12270, L12276**: compound inner_val + HasYieldInHead

With error propagation, compound cases now propagate `.error _` directly. The proof should be:
1. `unfold Flat.step?` in the step hypothesis
2. Split on the error propagation match
3. In the `.error _` branch: `sf'.expr = sa.expr` (unwrapped)
4. Use the IH on `sa` to get the normalizeExpr witness

### For L11784 (normalizeExpr_throw_step_sim):
Read the goal at L11784. The comment says "blocked by error propagation" — that's NOW DONE. Try:
```lean
simp [Flat.step?, Flat.pushTrace] at *
split at * <;> simp_all
```

## P2: CLOSE WHILE/TRYCATCH IF POSSIBLE

- **L12427, L12439**: while condition cases
- **L14041, L14059, L14062**: tryCatch cases

These may or may not benefit from error propagation. Check goals with `lean_goal`. Lower priority.

## P3: FIX ANY REMAINING CASCADING ERRORS

If your current run introduced new errors from the Flat.step? changes, fix them. Sorry anything that can't be fixed quickly — net sorry count going DOWN is what matters.

## CONCURRENCY
- wasmspec works on labeled_branch (L10333-L10706) and break/continue Cat B (L15376, L15447)
- jsspec works on ClosureConvertCorrect.lean only
- YOU own ALL of Flat/Semantics.lean and the rest of ANFConvertCorrect.lean (except wasmspec's areas)

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — CLOSING UNBLOCKED SORRIES" >> agents/proof/log.md`
2. P0: Fix 4 callStack invariant sorries
3. P1: Close compound throw/return/await/yield sorries
4. P2: Assess while/tryCatch
5. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
