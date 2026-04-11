# proof — DEPTH INDUCTION FOR COMPOUND HasThrowInHead (L11634)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 42 sorries. CC: 23. Lower: 0. Wasm: 0. Total: 65.
- Error propagation DONE in Flat/Semantics.lean — ALL compound `step?` cases drop wrapper on `.error`.
- **THE COMMENTS AT L11625-L11632 ARE WRONG.** Error propagation IS implemented.
- Last proof run: 2026-04-01. 10 DAYS AGO. Focus and deliver.

## P0: L11634 — COMPOUND HasThrowInHead

### Why it's sorry'd
`normalizeExpr_throw_step_sim` (L11491) handles `HasThrowInHead sf.expr`. Cases:
- `throw_direct` → handled (L11517-L11613, delegates to `normalizeExpr_throw_compound_case`)
- `return_some_arg`, `yield_some_arg`, `await_arg` → absurd via NoNestedAbrupt (L11614-L11616)
- `| _ =>` at L11617 → **SORRY at L11634** — 29 compound constructors (seq_left, let_init, etc.)

### The root problem
For compound cases (e.g., `seq_left ha` means `e = .seq a b` where `HasThrowInHead a`):
1. We need Steps from `{expr := e, ...}` producing the error
2. The IH should give Steps from `{expr := a, ...}` producing error
3. These need lifting through `.seq · b` context
4. Error propagation drops the `.seq` wrapper on error

BUT `normalizeExpr_throw_step_sim` is a flat theorem, not recursion. There is no IH available.

### FIX: Add depth induction

Create a new helper theorem that does depth induction:

```lean
private theorem normalizeExpr_throw_compound_step_sim
    (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
    (hthrow : HasThrowInHead e)
    -- e is NOT .throw itself (those are handled by throw_direct)
    (hnot_throw : ∀ arg, e ≠ .throw arg)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (.throw arg, m))
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (hewf : ExprWellFormed e env)
    (hna : NoNestedAbrupt e) :
    -- Produce steps from e (not from .throw e) that reach error
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs sf' ∧
      -- After stepping through e, we get the throw firing
      ... := by
  induction d with
  | zero => -- e.depth = 0, compound cases impossible
    cases e <;> (first | cases hthrow | simp [Flat.Expr.depth] at hd)
  | succ d ih =>
    cases hthrow with
    | seq_left ha =>
      -- e = .seq a b, HasThrowInHead a
      -- normalizeExpr (.seq a b) k = normalizeExpr a (fun t => ...)
      -- By ih on a (depth ≤ d), get Steps from {expr := a, ...}
      -- Lift through .seq · b using Steps_seq_ctx (non-error steps)
      -- Then use step?_seq_error for the final error step
      sorry
    | ...
```

### CONCRETE APPROACH — start with seq_left:

1. `lean_goal` at L11634 to see exact goal state with all hypotheses
2. `lean_hover_info` on `Steps_ctx_lift` (L2394) to understand its API
3. Note: `Steps_ctx_lift` requires `hnoerr` — it CANNOT lift error events
4. You need a NEW lifting lemma or decompose: lift non-error prefix, then add final error step separately
5. Error propagation lemmas exist: `step?_seq_error` (L2272), `step?_let_init_error` (L2284), `step?_unary_error` (L2296), etc.

### Key insight about the proof structure
The Steps from inner expression will be: [silent, silent, ..., error msg].
- Lift [silent, ...] through compound context using `Steps_ctx_lift`
- Then the last step in the compound context: use `step?_seq_error` etc. to show the compound drops wrapper

### ALTERNATIVE simpler approach
Instead of depth induction in `normalizeExpr_throw_step_sim`, restructure L11634:
1. Case split on what `e` (the original expression) is
2. For `e = .seq a b`: unfold `normalizeExpr (.seq a b) k` in `hnorm`
3. The normalizeExpr gives `normalizeExpr a (fun t => seq_cont)` = `.throw arg`
4. Use `normalizeExpr_throw_implies_hasThrowInHead` on `a` with the seq continuation
5. Recurse on the depth of `a` (which is strictly smaller than `e`)

Try BOTH with `lean_multi_attempt`:
```
["cases e <;> simp [ANF.normalizeExpr] at hnorm ⊢",
 "induction e using Flat.Expr.recOn"]
```

## P1: IF L11634 CRACKS → apply to L11785, L11791, L11958, L11964, L12116, L12122

Same pattern for return/await/yield compound cases. Template identical.

## SKIP: labeled_branch (wasmspec), CC (jsspec), while/tryCatch/if_branch, anfConvert_step_star

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound HasThrowInHead L11634 depth induction" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
