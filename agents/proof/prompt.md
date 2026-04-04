# proof — DECOMPOSE L7151 with by_cases NOW. You have been stuck for 4 runs.

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

## STATE: ANF has 22 sorries. You have been stuck for 4 RUNS. You have built infrastructure (Steps_*_ctx wrappers, HasReturnInHead) but CLOSED ZERO sorries. Time to produce RESULTS.

## YOUR TASK: Decompose L7151 with by_cases, then close the trivial-chain half

### Current sorry line numbers (UPDATED — lines shifted since last run):
- Group A (7): L6531, L6564, L6575, L6656, L6689, L6700, L6717 — PARKED (continuation-independence)
- Group D (8): L7151, L7154, L7304, L7307, L7477, L7480, L7631, L7634 — YOUR TARGET
- Group F (5): L7661, L7709, L7740, L7743, L7787 — DEFERRED
- Group G (2): L8165, L8217 — wasmspec owns these

### Step 1: Split L7151 into two sub-cases (DO THIS FIRST)

At L7151, inside `normalizeExpr_throw_step_sim`, `throw_direct` case:
- `sf.expr = .throw flat_arg`
- `flat_arg` is compound
- `hnorm' : (normalizeExpr flat_arg (fun t => pure (.throw t))).run n = .ok (.throw arg, m)`

Replace the `sorry` at L7151 with:
```lean
    | _ =>
      by_cases hth : HasThrowInHead flat_arg
      · -- nested throw: flat_arg itself contains a throw
        sorry -- NESTED_THROW: needs multi-step simulation through double error
      · -- no throw in head: flat_arg is a trivial chain
        have htc := no_throw_head_implies_trivial_chain flat_arg.depth flat_arg (Nat.le_refl _)
          (fun t => pure (.throw t)) arg n m hnorm' hth
        sorry -- TRIVIAL_CHAIN_IN_THROW: consume trivial chain in .throw [·] context
```

### Step 2: Close the TRIVIAL_CHAIN_IN_THROW sorry

Build `trivialChain_throw_steps` following the pattern of `trivialChain_consume_ctx` (around L1993):

```lean
private theorem trivialChain_throw_steps
    (fuel : Nat) (tc : Flat.Expr) (sf : Flat.State)
    (htc : isTrivialChain tc = true)
    (hcost : trivialChainCost tc ≤ fuel)
    (hsf : sf.expr = .throw tc)
    (hwf : ∀ x, VarFreeIn x tc → sf.env.lookup x ≠ none) :
    ∃ (v : Flat.Value) (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps sf evs sf' ∧
      sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.trace = sf.trace ++ evs ∧
      observableTrace evs = observableTrace [.error (Flat.valueToString v)] := by
  sorry -- induction on fuel, similar to trivialChain_consume_ctx
```

### Step 3: Apply same pattern to L7304 (return), L7477 (await), L7631 (yield)

Each needs the same by_cases + trivialChain helper. Do them ONE AT A TIME.

### DO NOT attempt L7154, L7307, L7480, L7634 yet
Those are the compound HasXInHead cases from the CALLER. Park them.

### Target: 22 → close at least 2 sorries. Even decomposing all 4 is progress.

## ACCOUNTABILITY: If you complete this run with ZERO sorry changes, you will be replaced.

## WORKFLOW:
1. `lean_goal` at L7151 to see exact proof state
2. Edit L7151: replace `sorry` with `by_cases` split
3. Build to verify it compiles
4. Write `trivialChain_throw_steps` with sorry body, build
5. Prove body by induction (follow `trivialChain_consume_ctx`)
6. Use it to close ¬HasThrowInHead sorry
7. Repeat for L7304, L7477, L7631

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
