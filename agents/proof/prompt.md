# proof — Close let_step_sim (L6763) then if_step_sim (L6842/6845/6849)

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

## YOUR IMMEDIATE TASK: let_step_sim (L6763)

### Step 1: Build `bindComplex_not_let` (copy `bindComplex_not_seq` at line 458)

`bindComplex_not_seq` is at line 458. It works because `bindComplex` produces `.seq fresh (k trivial)` — which is `.seq`, never `.let`. The EXACT SAME proof works for `.let`:

```lean
private theorem bindComplex_not_let (rhs : ANF.ComplexExpr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (name : String) (init body : ANF.Expr) :
    (ANF.bindComplex rhs k).run n ≠ .ok (.let name init body, m) := by
  show ANF.bindComplex rhs k n ≠ .ok (.let name init body, m)
  simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
             get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
             StateT.set, pure, Pure.pure, StateT.pure, Except.pure, getThe, MonadStateOf.get]
  cases hk : k (.var (toString "_anf" ++ toString (Nat.repr n))) (n + 1) with
  | error => simp [hk]
  | ok v => intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
```

Place this right after `bindComplex_not_seq` (after line 467).

### Step 2: Build `normalizeExpr_let_source` characterization

This follows the SAME pattern as `normalizeExpr_seq_while_first_family` (lines ~767-1068) but is MUCH simpler because we only need to show `.let` output implies `.let` input — not track what the first component is.

For each Flat.Expr constructor in normalizeExpr:
- Most use `bindComplex` → contradiction via `bindComplex_not_let`
- `.let fname finit fbody` → produces `.let` directly → ∃ witness found
- `.while_`, `.labeled`, `.tryCatch` → produce forms that aren't `.let` → contradiction

The theorem:
```lean
private theorem normalizeExpr_let_source
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (n m : Nat) (name : String) (rhs body : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (.let name rhs body, m)) :
    ∃ (fname : String) (finit fbody : Flat.Expr),
      e = .let fname finit fbody := by
  cases e with
  | «let» fname finit fbody => exact ⟨fname, finit, fbody, rfl⟩
  | lit v => -- k produces .trivial, .trivial ≠ .let
    simp [ANF.normalizeExpr] at hnorm
    -- hk gives (k (.litTrivial v)).run n = .ok (.trivial _, _), but hnorm says = .ok (.let _, _)
    have ⟨m', hkm⟩ := hk (.litTrivial v) n
    rw [hkm] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  | var name' => -- same: k produces .trivial
    simp [ANF.normalizeExpr] at hnorm
    have ⟨m', hkm⟩ := hk (.var name') n
    rw [hkm] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  -- ... for each remaining constructor: unfold normalizeExpr, show it calls bindComplex
  --     (contradiction) or produces non-.let form (contradiction)
  | _ => sorry -- Fill in per-constructor, each using bindComplex_not_let
```

You will need ~30 cases. Most are 2-3 lines using `bindComplex_not_let`. Use the `normalizeExpr_seq_while_first_family` as your template — it handles all the same cases.

### Step 3: Close let_step_sim at L6763

Once you have `normalizeExpr_let_source`, use it at L6763:
```lean
  have ⟨fname, finit, fbody, he_let⟩ := normalizeExpr_let_source sf.expr k hk n m name rhs body hnorm
  subst he_let
  -- Now sf.expr = .let fname finit fbody
  -- Flat.step? on .let: if finit is value, extend env; if not, step finit
  -- ANF.step? on .let: evalComplex rhs → extend env with result → continue with body
  -- rhs comes from normalizeExpr: rhs = .trivial initTriv (from the .let case of normalizeExpr)
  -- So evalComplex (.trivial initTriv) evaluates the trivial expression
  -- Match this with Flat evaluation of finit
```

### Step 4: if_step_sim (L6842, L6845, L6849) — SAME PATTERN

Build `normalizeExpr_if_source` (analogous to let_source):
- `.if` output can ONLY come from Flat `.if` constructor
- Then case-split on cond being true/false/error

### Step 5 (stretch): tryCatch_step_sim (L6873)

Same characterization pattern for `.tryCatch`.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
- seq_step_sim — blocked on SimRel generalization

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
