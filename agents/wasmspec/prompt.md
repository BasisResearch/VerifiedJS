# wasmspec — Help proof agent close TRIVIAL_CHAIN_CONNECT sorry

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean

## BACKGROUND
The proof agent has been stuck for 7+ runs. It needs a helper lemma to close the TRIVIAL_CHAIN_CONNECT sorry. You will write this helper.

## YOUR TASK: Write trivialChain_normalizeExpr_trivialOf

### What the proof agent needs

At the TRIVIAL_CHAIN_CONNECT sorry (grep for it in ANFConvertCorrect.lean), the proof state has:
- `e : Flat.Expr` with `isTrivialChain e = true`
- `normalizeExpr e (fun t => pure (.throw t))` produced `.throw arg`
- `trivialChain_throw_steps` gave flat value `v`

The GAP: no lemma connects `arg` (the ANF.Trivial) to `e` (the Flat.Expr).

### Step 1: Write the helper lemma

Add this BEFORE `normalizeExpr_throw_compound_case` in ANFConvertCorrect.lean:

```lean
/-- When e is a trivial chain (lit/var/this), normalizeExpr e k calls k with
    the trivial representation, and evalTrivial on that trivial matches
    the flat evaluation. -/
private theorem trivialChain_normalizeExpr_produces_trivial
    (e : Flat.Expr) (n : Nat)
    (htc : isTrivialChain e = true)
    (h_simple : ∀ x, VarFreeIn x e → Flat.Env.lookup env x ≠ none) :
    -- For base cases only (no seq needed for throw since normalizeExpr
    -- handles seq via bindComplex which lifts through the continuation)
    match e with
    | .lit v => ∃ t, (fun t => pure (ANF.Expr.throw t) : ANF.Trivial → ANF.ConvM ANF.Expr) t
                  ... -- produces the right trivial
    | .var x => ...
    | .this => ...
```

Actually, simpler: just prove by cases in place. Use `lean_goal` at the sorry to see what's needed, then help the proof agent by writing a targeted cases proof.

### Step 2: Actual approach — CASES on e at the sorry site

Rather than writing a separate lemma, check with `lean_goal` what `e` can be when `isTrivialChain e = true`. The answer is: `.lit`, `.var`, `.this`, `.seq a b` (recursively).

For the simplest path: write a proof that does:
```lean
cases e with
| lit v => simp [ANF.normalizeExpr, pure, Pure.pure, StateT.pure] at hnorm'; ...
| var x => simp [ANF.normalizeExpr, pure, Pure.pure, StateT.pure] at hnorm'; ...
| this => simp [ANF.normalizeExpr, pure, Pure.pure, StateT.pure] at hnorm'; ...
| seq a b => simp [isTrivialChain] at htc; ...
| _ => simp [isTrivialChain] at htc
```

### Step 3: Build and verify

`lake build VerifiedJS.Proofs.ANFConvertCorrect`

### COORDINATE WITH PROOF AGENT
Check `git diff` before editing. If proof agent has uncommitted changes at the same location, work around them. The proof agent is focused on the same sorry — your helper goes BEFORE it.

### Group G: STILL PARKED
L8797 and L8850 unchanged. No action needed.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
