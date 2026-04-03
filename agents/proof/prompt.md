# proof — Close if_step_sim (L7062/7065/7077/7079), then tryCatch_step_sim

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 30 sorry occurrences (grep -c). Lower 0 ✓. CC — OTHER AGENTS OWN IT.

## ⚠️ YOU KEEP CRASHING — READ THIS ⚠️
Your last 2 runs crashed (exit code 1) after <10 minutes. Likely cause: OOM from building too much at once.
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` (L6785) entirely.

## YOUR IMMEDIATE TASK: normalizeExpr_if_source characterization lemma

The if_step_sim sorries are at approximately L7062, L7065, L7077, L7079. Run `grep -n sorry VerifiedJS/Proofs/ANFConvertCorrect.lean` to get CURRENT line numbers.

`bindComplex_not_if` ALREADY EXISTS (line ~469). The characterization approach works for `.if`.

### Step 1: Build `normalizeExpr_if_source` characterization

Follow the SAME pattern as `normalizeExpr_seq_while_first_family` (lines ~767-1068).

```lean
private theorem normalizeExpr_if_source
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (n m : Nat) (cond : ANF.Trivial) (then_ else_ : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (.if cond then_ else_, m)) :
    ∃ (fc : Flat.Expr) (ft fe : Flat.Expr),
      e = .if fc ft fe := by
  cases e with
  | «if» fc ft fe => exact ⟨fc, ft, fe, rfl⟩
  | lit v =>
    simp [ANF.normalizeExpr] at hnorm
    have ⟨m', hkm⟩ := hk (.litTrivial v) n
    rw [hkm] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  | var name' =>
    simp [ANF.normalizeExpr] at hnorm
    have ⟨m', hkm⟩ := hk (.var name') n
    rw [hkm] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  -- For constructors using bindComplex: unfold normalizeExpr, use bindComplex_not_if
  -- For .seq, .while_, .let, .tryCatch, .labeled: unfold normalizeExpr, show they don't produce .if
  | _ => sorry -- Fill per-constructor
```

For each remaining constructor:
- **Uses `bindComplex`** (unary, binary, call, getProp, etc.): unfold normalizeExpr, show result goes through bindComplex, use `bindComplex_not_if`
- **`.seq a b`**: normalizeExpr produces seq/while, not if → use `normalizeExpr_seq_while_first` (already proved)
- **`.while_ c d`**: normalizeExpr produces while, not if
- **`.let`, `.tryCatch`, `.labeled`**: produce their own form, not if
- **`.return`, `.throw`, `.break`, `.continue`, `.await`, `.yield`**: produce their form + continuation

Use `normalizeExpr_seq_while_first_family` as the structural template.

### Step 2: Use normalizeExpr_if_source to close if_step_sim sub-sorries

```lean
have ⟨fc, ft, fe, he_if⟩ := normalizeExpr_if_source sf.expr k hk n m cond then_ else_ hnorm
subst he_if
-- Now sf.expr = .if fc ft fe, match flat semantics
```

### Step 3: tryCatch_step_sim — SAME PATTERN
Build `normalizeExpr_tryCatch_source` using `bindComplex_not_tryCatch` (line ~480).

## SKIP THESE:
- `let_step_sim` (L6785) — bindComplex PRODUCES .let, characterization WRONG
- `seq_step_sim` — blocked on SimRel while-loop generalization
- ClosureConvertCorrect.lean — other agents own it
- LowerCorrect.lean — DONE (0 sorries)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
