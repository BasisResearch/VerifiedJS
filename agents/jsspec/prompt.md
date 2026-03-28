# jsspec — ANF HELPER LEMMAS (CRITICAL PATH)

## STATUS: proof agent is FINALLY pivoting to ANF. It needs normalizeExpr inversion lemmas urgently.

## PRIORITY 0: normalizeExpr inversion lemmas

The proof agent needs to invert `hnorm : StateT.run (ANF.normalizeExpr sf.expr k) n = Except.ok (ANF.Expr.break label, m)` to conclude `sf.expr = Flat.Expr.break label`.

Write these lemmas in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_norm_inv.lean`:

```lean
-- 1. normalizeExpr (.break label) k always produces .break label (ignores k)
theorem normalizeExpr_break (label : Option String) (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n : Nat) :
    StateT.run (ANF.normalizeExpr (.break label) k) n = Except.ok (.break label, n)

-- 2. If normalizeExpr e k produces .break label, then e = .break label
theorem normalizeExpr_break_inv (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat) (label : Option String)
    (h : StateT.run (ANF.normalizeExpr e k) n = Except.ok (.break label, m)) :
    e = .break label

-- 3. Same for continue
theorem normalizeExpr_continue_inv (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat) (label : Option String)
    (h : StateT.run (ANF.normalizeExpr e k) n = Except.ok (.continue label, m)) :
    e = .continue label
```

Use `lean_hover_info` on `ANF.normalizeExpr` to understand the definition, then prove each.
Also write similar lemmas for throw, return, yield, await.

## PRIORITY 1: ANF.step? simp lemmas

```lean
@[simp] theorem ANF_step?_break (label env heap trace) :
    ANF.step? ⟨.break label, env, heap, trace⟩ = some (.silent, ANF.pushTrace ⟨.trivial .litUndefined, env, heap, trace⟩ .silent)

@[simp] theorem ANF_step?_continue (label env heap trace) :
    ANF.step? ⟨.continue label, env, heap, trace⟩ = some (.silent, ANF.pushTrace ⟨.trivial .litUndefined, env, heap, trace⟩ .silent)
```

Verify each with `lean_run_code` or `lake env lean` on the staging file.

## PRIORITY 2: Flat.Step lemmas for break/continue

The proof agent also needs: if sf.expr = .break label, then Flat.Step sf .silent {sf with expr := .lit .undefined, trace := sf.trace ++ [.silent]}.

## What NOT to do:
- Do NOT edit main proof files
- Do NOT run full `lake build`

## Log progress to agents/jsspec/log.md.
