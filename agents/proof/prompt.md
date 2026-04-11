# proof — COMPOUND HasThrowInHead (L11634) IS NOW PROVABLE

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 41 sorries. CC: 15. Lower: 0. Total: 56.
- Dead code deleted: Steps_{throw,return_some,await,yield_some}_pres (4 sorries removed).
- Error propagation DONE in Flat/Semantics.lean.

## KEY FACT: THE COMMENTS AT L11619-L11633 ARE WRONG

The comments say "Flat.step? does not propagate error events" — THIS IS OUTDATED AND FALSE.

Error propagation WAS ADDED. For ALL compound expressions (seq, if, let, call, etc.), Flat.step? now does:
```lean
match t with
| .error _ =>
    let s' := pushTrace { s with expr := sub_state.expr, env := sub_state.env, heap := sub_state.heap } t
    some (t, s')    -- DROPS the compound wrapper
| _ =>
    let s' := pushTrace { s with expr := compound_wrapper sub_state.expr ..., ... } t
    some (t, s')    -- KEEPS the compound wrapper
```

This means stepping `.seq (.throw (.lit v)) b` with error now gives `s'.expr = .lit .undefined` (NOT `.seq (.lit .undefined) b`).

## P0: FIX L11634 (compound HasThrowInHead — THE BIG ONE)

This sorry is at the `| _ =>` catch-all in `normalizeExpr_throw_step_sim` (line ~11617).

The proof needs to handle 29 HasThrowInHead compound constructors (seq_left, seq_right, let_init, etc.). For EACH compound case:

1. The inner expression has HasThrowInHead recursively
2. By IH (from the HasThrowInHead hypothesis), there exist Flat Steps from the inner expr that produce the error event
3. These inner Steps need to be LIFTED through the compound context (using `Steps_ctx_lift_pres` or similar)
4. With error propagation, the final step UNWRAPS the compound, giving `s'.expr = .lit .undefined`

**Proof sketch for seq_left case** (`.throw (.seq a b)` where `a` has throw in head):
```lean
| seq_left ha =>
  -- ha : HasThrowInHead a
  -- By IH on ha, get Steps from {expr := .throw a, ...} producing error
  -- Lift through .throw context: Steps from .throw a → Steps from .throw (.seq a b)?
  -- Actually: normalizeExpr (.seq a b) k_throw = normalizeExpr a (fun t => ...)
  -- The key: normalizeExpr recurses into a, and k wraps with throw
  -- Need: Steps from .seq a b in the throw context reach the error
  sorry -- try this case first
```

**APPROACH**:
1. `lean_goal` at L11634 to see the EXACT goal with error propagation
2. Try `lean_multi_attempt` at L11634 with: `["cases hthrow", "rcases hthrow with _ | _ | _"]`
3. Pick ONE compound case (e.g., seq_left). Write proof for that single case.
4. If it works, apply pattern to others.

## P1: IF L11634 MAKES PROGRESS, try L11785, L11791, L11958, L11964, L12116, L12122

These are the SAME pattern in return/await/yield versions:
- L11785: return compound inner_val
- L11791: compound HasReturnInHead
- L11958: await compound inner_arg
- L11964: compound HasAwaitInHead
- L12116: yield compound inner_val
- L12122: compound HasYieldInHead

## SKIP: Do NOT work on these
- L10361-L10734 — wasmspec owns labeled_branch
- L12183, L12178, L13912, L13910, L13922 — while/tryCatch/if_branch (different blockers)
- L15344, L15355, L15574, L15645 — anfConvert_step_star (needs everything else first)

## CONCURRENCY
- wasmspec works on labeled_branch (L10183-L10556)
- jsspec works on ClosureConvertCorrect.lean only
- YOU own everything else in ANFConvertCorrect.lean

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — compound HasThrowInHead L11634" >> agents/proof/log.md`
2. `lean_goal` at L11634
3. Try ONE compound sub-case
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
5. EXIT after P0.
