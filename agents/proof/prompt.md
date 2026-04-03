# proof — Close let_step_sim then if_step_sim with characterization lemmas

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 24 sorries (was 22, +2 from if decomposition). Lower 0 ✓. CC — OTHER AGENTS OWN IT.

## SKIP seq_step_sim — CONFIRMED BLOCKED on SimRel while-loop issue.

## YOUR IMMEDIATE TASK: let_step_sim (L6763) — MOST TRACTABLE

### KEY INSIGHT: normalizeExpr `.let` comes ONLY from Flat `.let`

Look at line 307-317 in ANFConvertCorrect.lean:
```lean
| «let» name init body =>
    normalizeExpr init (fun initTriv => do
        let bodyExpr ← normalizeExpr body k
        pure (.let name (.trivial initTriv) bodyExpr))
```

The continuation `(fun initTriv => do ... pure (.let name (.trivial initTriv) bodyExpr))` is the ONLY thing that produces `.let` — `bindComplex` never produces `.let` (it produces `.seq` or `.trivial`). The outer `normalizeExpr init` with this continuation recurses into subexpressions but the `.let` output always comes from this continuation.

### Step 1: Prove `normalizeExpr_let_source`

This is MUCH simpler than the seq characterization because `.let` can ONLY come from Flat `.let`:

```lean
private theorem normalizeExpr_let_source
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (n m : Nat) (name : String) (rhs body : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (.let name rhs body, m)) :
    ∃ (fname : String) (finit fbody : Flat.Expr),
      e = .let fname finit fbody := by
  -- Since hk says k always produces .trivial, and .let ≠ .trivial,
  -- k cannot be the source of .let. So it must come from the .let case of normalizeExpr.
  -- Use normalizeExpr_never_trivial (line ~112): normalizeExpr e k with trivial-preserving k
  -- never produces .trivial directly — WAIT, it's the opposite.
  -- Actually: k produces .trivial, but normalizeExpr wraps it.
  -- The point: trace through each Flat.Expr case and show only .let produces .let output.
  -- For most cases: normalizeExpr recurses with a continuation that calls bindComplex.
  --   bindComplex produces .seq or result of k. k produces .trivial. Neither is .let.
  -- Only .let case: continuation produces .let directly.
  sorry
```

ACTUALLY — the simpler approach: you already proved `bindComplex_not_seq`. You need `bindComplex_not_let`:

```lean
private theorem bindComplex_not_let
    (complex : ANF.Complex) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (name : String) (rhs body : ANF.Expr)
    (h : (ANF.bindComplex complex k).run n = .ok (.let name rhs body, m)) : False := by
  simp [ANF.bindComplex, bind, Bind.bind, StateT.bind, Except.bind,
        pure, Pure.pure, StateT.pure, Except.pure] at h
```

This should close by `simp` because `bindComplex` produces `.seq fresh (k trivial)` — which is `.seq`, never `.let`.

Then the characterization follows by induction on `e`, same structure as `normalizeExpr_seq_while_first_family` but each case is simpler (most are contradictions via `bindComplex_not_let`).

### Step 2: Close let_step_sim at L6763

Once you know `sf.expr = .let fname finit fbody`:
1. `Flat.step?` on `.let fname finit fbody` evaluates `Flat.step? { sf with expr := finit }` or (if finit is a value) extends env
2. Show `ANF.step?` on `.let name rhs body` does the corresponding thing
3. Key: `rhs = .trivial initTriv` (from normalization), so ANF `evalComplex rhs` = evaluate `initTriv`
4. Flat evaluates `finit` → gets value → extends env with `fname` → continues with `fbody`
5. ANF evaluates `.trivial initTriv` → gets value → extends env with `name` → continues with `body`
6. Show `fname = name`, values correspond, `body` is `normalizeExpr fbody k` applied to rest

### Step 3: if_step_sim (L6842, L6845, L6849)

Same approach. `.if` comes ONLY from Flat `.if` (line 318-328). Build `normalizeExpr_if_source`, then:
- L6842 (then): Flat `.if` with true cond steps to then branch. Show `thenExpr = normalizeExpr then_ k`, establish SimRel.
- L6845 (else): Same but false cond → else branch.
- L6849 (error): `evalTrivial` error means Flat eval of cond also errors.

### Step 4 (if time): tryCatch_step_sim (L6873)

`.tryCatch` comes ONLY from Flat `.tryCatch` (line 345-353). Same characterization pattern.

## PRIORITY 2: Compound cases (~14 sorries, L5884-L6736)

These `| _ => sorry` in HasAwait/Return/Yield/Throw proofs need per-constructor case analysis. Lower priority than let/if/tryCatch.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
- seq_step_sim — blocked on SimRel generalization

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
