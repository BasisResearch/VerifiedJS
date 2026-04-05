# wasmspec — Build compound sub-expression IH infrastructure for ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.8GB available right now.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9485 (tryCatch step sim) and L9079-9084 (let compound)
- **YOU** insert new infrastructure ABOVE L9027 (around line 9020)
- **YOU** can also edit L9367/9368 and L9440/9441
- DO NOT touch lines 9027-9090 or 9475-9500

## STATUS: STUCK 3 RUNS on L9367-9441. APPROACH CHANGE REQUIRED.

The exfalso approach DOES NOT WORK — compound condition cases ARE REACHABLE.
The Flat machine has the ORIGINAL un-normalized expression. When normalizeExpr(.if cond then else)
normalizes cond to trivial `t`, the Flat machine still has compound `cond` and needs MULTIPLE
steps to evaluate it. This is a multi-step simulation problem.

## ROOT CAUSE: Missing Induction Hypothesis

ALL compound sorry cases in ANF share the same problem: the per-constructor `normalizeExpr_*_step_sim`
theorems handle lit/var/this sub-expressions but `sorry` ALL compound sub-expressions because they
lack an IH for recursive simulation.

The fix: build a depth-based strong induction infrastructure that lets compound sub-expression
cases call the simulation recursively on smaller expressions.

## YOUR TASK: Restructure anfConvert_step_star with depth induction

Currently `anfConvert_step_star` (L10409) does a flat case split on `sa.expr` and dispatches
to per-constructor theorems. It has NO induction, so per-constructor theorems get NO IH.

### Approach: Add depth parameter + IH threading

1. **Read** `anfConvert_step_star` (L10409-L10488+) carefully to understand its structure.

2. **Add** an IH parameter to `normalizeExpr_if_step_sim` (L9275):
```lean
private theorem normalizeExpr_if_step_sim
    (sf : Flat.State) (s : Flat.Program) (t : ANF.Program)
    (h_convert : ANF.convert s = .ok t)  -- ADD THIS
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (cond : ANF.Trivial) (then_ else_ : ANF.Expr)
    -- ADD: IH for sub-expressions with smaller depth
    (ih_sub : ∀ (sf_sub : Flat.State),
      sf_sub.expr.depth < sf.expr.depth →
      ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n' m' : Nat) (anf' : ANF.Expr),
      (ANF.normalizeExpr sf_sub.expr k').run n' = .ok (anf', m') →
      (∀ t' n'', ∃ m'', (k' t').run n'' = .ok (.trivial t', m'')) →
      ExprWellFormed sf_sub.expr sf_sub.env →
      ∀ ... → ∃ sf' evs, Flat.Steps sf_sub evs sf' ∧ ...)
    (hnorm : ...) -- rest unchanged
```

3. **Restructure** `anfConvert_step_star` to use `Nat.strongRecOn sf.expr.depth`:
```lean
private theorem anfConvert_step_star ... := by
  intro sa sf ev sa' hrel hewf hna hstep
  -- Strong induction on sf.expr.depth
  have : ∀ (d : Nat) (sf : Flat.State), sf.expr.depth ≤ d → ... := by
    intro d; induction d with
    | zero => ...
    | succ d ih => ...
  exact this sf.expr.depth sf (Nat.le_refl _) ...
```

### SIMPLEST FIRST: Just add ih_sub to normalizeExpr_if_step_sim

Don't restructure everything. Start minimal:

1. Add `ih_sub` parameter to `normalizeExpr_if_step_sim` signature
2. In the compound case at L9367, USE `ih_sub`:
   - The Flat expression is `.if c_flat then_flat else_flat` where c_flat is compound
   - `c_flat.depth < (.if c_flat then_flat else_flat).depth` (by Flat.Expr.depth definition)
   - normalizeExpr of the if produces a normalized condition as a trivial
   - Use ih_sub on `⟨c_flat, env, heap, trace, funcs, cs⟩` to simulate the condition evaluation
   - Then step the resulting `.if (.lit v) then_flat else_flat` to the branch
3. Update the call site in `anfConvert_step_star` to pass `ih_sub` (this will sorry initially — that's OK)
4. Verify with LSP that L9367 closes with the IH

### CRITICAL: This is infrastructure work

It's OK if adding ih_sub creates a sorry at the CALL SITE in anfConvert_step_star.
Trading 4 sorry at L9367-9441 for 1 sorry at the call site is PROGRESS.
The call-site sorry can be closed in the next run by adding the strong induction to anfConvert_step_star.

## STEP-BY-STEP PLAN
1. `lean_goal` at L9367 — understand exact proof state
2. `lean_hover_info` on `normalizeExpr_if_step_sim` — get current signature
3. Add `ih_sub` parameter to signature with correct type
4. Use `ih_sub` at L9367 to close compound condition case
5. Use same approach for L9368 (HasIfInHead compound cases)
6. Update call site in `anfConvert_step_star` — sorry the ih_sub argument for now
7. Repeat for L9440/9441 (false branch — structurally identical)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
