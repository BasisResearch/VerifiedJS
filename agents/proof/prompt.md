# proof — Close let_step_sim and if_step_sim, then compound cases

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

### Step 1: Build `normalizeExpr_let_head_family` characterization lemma

Follow the EXACT pattern of `normalizeExpr_seq_while_first_family` (lines ~767-1068).

The lemma you need:
```lean
private theorem normalizeExpr_let_head_family
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (n m : Nat) (name : String) (rhs body : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (.let name rhs body, m)) :
    ∃ (fname : String) (finit fbody : Flat.Expr),
      e = .let fname finit fbody ∨ <other cases that produce .let>
```

To figure out WHICH Flat expressions can produce `.let`:
1. `lean_hover_info` on normalizeExpr at the `.let` case (~line 200-300 range in ANF definition)
2. Check: does bindComplex ever produce `.let`? Use `lean_hover_info` on bindComplex
3. The key insight: normalizeExpr's `.let` case is `| .let name init body => normalizeExpr init (fun initTriv => ...)` which produces `.let`

### Step 2: Use the characterization to close let_step_sim (L6763)

Once you know sf.expr must be `.let fname finit fbody`:
1. Flat.step? on `.let` evaluates `finit`, extends env
2. ANF.step? on `.let` evaluates `rhs` via evalComplex, extends env
3. Show the results correspond: evalComplex on ANF side matches Flat eval on flat side
4. Establish ANF_SimRel for the resulting body states

### Step 3: Build `normalizeExpr_if_head_family` and close if_step_sim (L6842, L6845, L6849)

Same pattern. normalizeExpr produces `.if` from Flat `.if`:
```
| .if cond then_ else_ =>
    normalizeExpr cond (fun condTriv => do
      let thenExpr ← normalizeExpr then_ k
      let elseExpr ← normalizeExpr else_ k
      pure (.if condTriv thenExpr elseExpr))
```

For if_step_sim:
- L6842 (then branch): Show flat `.if` steps to then_ when toBoolean = true
- L6845 (else branch): Show flat `.if` steps to else_ when toBoolean = false
- L6849 (error): Show evalTrivial error propagates

### Step 4 (if time): tryCatch_step_sim (L6873) — same characterization pattern

## PRIORITY 2: Compound cases (~14 sorries, L5884-L6736)

These `| _ => sorry` cases in HasAwaitInHead/HasReturnInHead/HasYieldInHead/HasThrowInHead proofs need case analysis on the compound expression form (seq, let, assign, if, call, etc.). Each compound case needs:
1. Show the compound form has the head expression at an eval context position
2. Show inner stepping preserves the head property
3. Use induction on depth

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
- seq_step_sim — blocked on SimRel generalization

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
