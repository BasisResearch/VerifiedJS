# proof — ADD NoNestedAbrupt PRECONDITION TO GROUP D THEOREMS

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

## STATE: ANF has 23 sorry lines. You correctly identified that Group D theorems are FALSE for nested abrupt completions. NOW FIX THEM.

## THE PROBLEM (you discovered this)
`normalizeExpr_throw_step_sim` etc. claim that Flat.Steps produce observable events matching one ANF error event. But for `throw(throw(x))`, Flat produces TWO error events while ANF short-circuits to one. The theorem is FALSE without restricting the input.

## YOUR TASK: Define NoNestedAbrupt and restructure Group D

### Step 1: Define NoNestedAbrupt (DO THIS FIRST)

Add this near the top of the file (before the step_sim theorems, around L6500):

```lean
/-- An expression has no nested abrupt completions:
    throw/return/yield/await sub-expressions don't themselves contain
    throw/return/yield/await in head position. This is a natural invariant
    of JavaScript programs where these are statements, not expressions. -/
inductive NoNestedAbrupt : Flat.Expr → Prop where
  | lit : NoNestedAbrupt (.lit v)
  | var : NoNestedAbrupt (.var x)
  | this : NoNestedAbrupt .this
  | throw (arg : Flat.Expr) (harg : isTrivialChain arg = true ∨ arg.isValue) :
      NoNestedAbrupt (.throw arg)
  | return_ (arg : Flat.Expr) (harg : isTrivialChain arg = true ∨ arg.isValue) :
      NoNestedAbrupt (.return_ arg)
  | yield (arg : Flat.Expr) (harg : isTrivialChain arg = true ∨ arg.isValue) :
      NoNestedAbrupt (.yield arg)
  | await (arg : Flat.Expr) (harg : isTrivialChain arg = true ∨ arg.isValue) :
      NoNestedAbrupt (.await arg)
  | seq (a b : Flat.Expr) (ha : NoNestedAbrupt a) (hb : NoNestedAbrupt b) :
      NoNestedAbrupt (.seq a b)
  -- Add cases for ALL other Flat.Expr constructors, each requiring NoNestedAbrupt on sub-exprs
```

Build to verify it compiles.

### Step 2: Add NoNestedAbrupt as hypothesis to Group D theorems

For each of `normalizeExpr_throw_step_sim`, `normalizeExpr_return_step_sim`, `normalizeExpr_await_step_sim`, `normalizeExpr_yield_step_sim`, add:
```lean
(hna : NoNestedAbrupt sf.expr)
```

### Step 3: Close the HasXInHead compound sorries via exfalso

With `NoNestedAbrupt (.throw flat_arg)`, we know `flat_arg` is a trivial chain or value.

For the `HasXInHead compound` sorries (~L7054, L7336, L7509, L7663):
- `NoNestedAbrupt (.throw compound_expr)` gives `isTrivialChain compound_expr ∨ isValue compound_expr`
- If trivial chain: `HasThrowInHead (trivialChain)` is false (lit/var/this don't have abrupt in head)
- If value: `HasThrowInHead value` is false
- Both cases: `exfalso`

These 4 sorries should close EASILY with NoNestedAbrupt. Do them FIRST.

### Step 4: Close the trivial-chain/value direct sorries

For the `*_direct compound` sorries (~L7050, L7183, L7333, L7506):
- If trivial chain: use existing `trivialChain_consume_ctx` + `Steps_throw_ctx`
- If value: `.throw val` steps directly in one step

### IMPORTANT: Update callers
After adding NoNestedAbrupt, `anfConvert_step_star` needs to supply the proof. Add `sorry` at call sites — we'll prove those later. Better to have honest small sorries.

### Group line numbers (VERIFY WITH lean_goal — lines may have shifted):
- Group D: ~L7050, L7054, L7183, L7333, L7336, L7506, L7509, L7660, L7663
- Group A (PARKED): L6531, L6564, L6575, L6656, L6689, L6700, L6717
- Group F (DEFERRED): L7690, L7738, L7769, L7772, L7816
- Group G (PARKED): L8195, L8248

### DO NOT TOUCH: Groups A, F, G

### Target: 23 → 15 (close 8 Group D sorries, may add 1-2 at caller sites)

## ACCOUNTABILITY: You have been stuck for 5+ runs. You correctly diagnosed the problem (false theorems). Now FIX IT by adding the precondition and closing sorries.

## WORKFLOW:
1. `lean_goal` at ~L7050 to verify current proof state
2. Define `NoNestedAbrupt` inductive type (build to verify)
3. Add `hna : NoNestedAbrupt sf.expr` to `normalizeExpr_throw_step_sim`
4. Close HasThrowInHead compound sorry via exfalso (EASY — 1 sorry)
5. Close trivial-chain direct sorry using existing infra (1 sorry)
6. Build to verify
7. Repeat for return (~L7183/L7336), await (~L7333/L7509), yield (~L7506/L7663)
8. Build full file

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
