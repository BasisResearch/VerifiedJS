# proof — PIVOT: Close ¬HasThrowInHead sub-case of L7122 first, then pattern-match for return/await/yield

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

## STATE: ANF has 22 sorries. You have built excellent infrastructure over 4 runs but closed 0 Group D sorries. Time to DECOMPOSE and close sub-cases.

## YOUR TASK: Decompose L7122 using Classical.em, then close the ¬HasThrowInHead half

### The problem at L7122

At L7122, inside `normalizeExpr_throw_step_sim`, `throw_direct` case:
- `sf.expr = .throw flat_arg`
- `flat_arg` is compound (not lit/var/this/break/continue — those are handled above)
- `hnorm' : (normalizeExpr flat_arg (fun t => pure (.throw t))).run n = .ok (.throw arg, m)`

You need Flat.Steps from `{expr := .throw flat_arg, env, heap, trace, funcs, cs}` to a terminal state.

### Step 1: Split L7122 into two sub-cases

Replace the `sorry` at L7122 with:
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

**This alone is worth doing** — it decomposes 1 opaque sorry into 2 categorized ones.

### Step 2: Close the TRIVIAL_CHAIN_IN_THROW sorry

You have `htc : isTrivialChain flat_arg = true`. A trivial chain is a `.seq` spine of `.lit`/`.var`/`.this` leaves. In the `.throw [·]` context, the inner expression steps (resolving vars to values, discarding seq left operands) until reaching a value. Then `.throw (.lit v)` produces the error event.

Build a helper `trivialChain_throw_steps` (analogous to `trivialChain_consume_ctx` at L1993 but for the `.throw [·]` context instead of `wrapSeqCtx`):

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

This is a standalone lemma you can build and test independently. Then use it to close the TRIVIAL_CHAIN_IN_THROW sorry.

### Step 3: Apply same pattern to L7275, L7448, L7602

These are the same structure but for `.return (some [·])`, `.await [·]`, `.yield (some [·])`. Each needs:
1. `by_cases` on HasXInHead
2. `no_X_head_implies_trivial_chain` (you may need to prove these, or the existing `no_throw_head_implies_trivial_chain` might generalize)
3. A `trivialChain_X_steps` helper

### DO NOT attempt L7125, L7278, L7451, L7605 yet
Those are the compound HasXInHead cases from the CALLER and need a fundamentally different approach (multi-step simulation through compound expressions). Park them.

### Target: 22 sorries → 24 (decomposition) → 20 (close 4 trivial chain halves)

Even just Step 1 (decomposing 4 sorries into 8 categorized ones) is valuable progress.

## WORKFLOW:
1. Edit L7122: replace `sorry` with `by_cases` split
2. Build to verify it compiles
3. Write `trivialChain_throw_steps` (start with sorry body, build signature)
4. Prove `trivialChain_throw_steps` by induction on fuel (follow `trivialChain_consume_ctx` pattern)
5. Use it to close the ¬HasThrowInHead sorry at L7122
6. Repeat for L7275, L7448, L7602

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
