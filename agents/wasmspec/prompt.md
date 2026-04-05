# wasmspec — Close normalizeExpr_if_branch_step sorries (L10559-10629)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.6GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11200-11360 (tryCatch) and L12400-12717 (break/continue/return)
- **YOU** own L8000-10912 (normalizeExpr step sim infrastructure)
- DO NOT touch lines outside your range

## YOUR ZONE: 36 sorries in L8000-10898. CLOSE THEM.

## IMMEDIATE TARGETS — GROUP E FIRST (5 sorries, L10615-10628)

These all follow the EXACT same pattern as the proven `seq_left` case (L10590-10607). Copy that pattern:

### TEMPLATE (from seq_left at L10590):
```lean
    | let_init h_init =>
      rename_i name init body
      simp only [ANF.normalizeExpr_let'] at hnorm
      have hinit_depth : init.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      obtain ⟨sf_init, evs_init, hsteps_init, hsil_init, henv_init, hheap_init, hfuncs_init, hcs_init,
        htrace_init, hpres_init, ⟨n_init, m_init, hnorm_init⟩, hewf_init⟩ :=
        ih init hinit_depth h_init env heap trace funcs cs _ n m cond then_ else_ v
          hnorm (fun x hfx => hewf x (VarFreeIn.let_init _ _ _ _ hfx)) heval hbool
      obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
        Steps_let_init_ctx name body hsteps_init
          (fun ev hev msg => by rw [hsil_init ev hev]; exact Core.TraceEvent.noConfusion)
          hpres_init
      refine ⟨ws, evs_init, hwsteps, hsil_init, hwenv.trans henv_init, hwheap.trans hheap_init,
        hwfuncs, hwcs, by rw [hwtrace, htrace_init], ?_, ?_, ?_⟩
      · sorry -- hpres (same as all other hpres sorries)
      · exact ⟨n_init, m_init, by rw [hwexpr]; simp only [ANF.normalizeExpr_let']; exact hnorm_init⟩
      · sorry -- ExprWellFormed (same pattern)
```

For each case, adapt:
- **L10615 let_init**: `Steps_let_init_ctx name body`, `VarFreeIn.let_init`, `normalizeExpr_let'`
- **L10619 throw_arg**: `Steps_throw_ctx`, `VarFreeIn.throw_arg`, `normalizeExpr_throw'`
- **L10622 return_some_arg**: `Steps_return_some_ctx`, `VarFreeIn.return_some_arg`, `normalizeExpr_return_some'`
- **L10625 await_arg**: `Steps_await_ctx`, `VarFreeIn.await_arg`, `normalizeExpr_await'`
- **L10628 yield_some_arg**: `Steps_yield_some_ctx delegate`, `VarFreeIn.yield_some_arg`, `normalizeExpr_yield_some'`

Check signatures with `lean_hover_info` at each `Steps_*_ctx` before writing. The key is matching the argument order.

## AFTER GROUP E: GROUP F (L10629 exotic cases)
Binary, unary, getProp, etc. should be contradictions — these can't have HasIfInHead:
```lean
lean_multi_attempt at L10629
["next => cases hif", "next h => cases h"]
```

## AFTER GROUP F: GROUP A (hpres, L10559/10583/10605) + GROUP C (ExprWellFormed L10607)
These repeat across all cases. Once you prove one, copy it everywhere.
For hpres: the Steps_*_ctx lemmas should give preservation directly. Check the `hpres_a` and `hpres_init` structures.

## AFTER hpres: GROUP D (L10611 seq_right) and GROUP B (L10567 trivialChain)
- L10611: `Classical.em (HasIfInHead a)` → true: IH on a; false: trivialChain_eval_value on a + IH on b
- L10567: `trivialChain_if_true_sim` directly

## FINALLY: L10668 (false version) — mechanically copy true → false substitutions
Then UNLOCK sorries (L10773-10898) cascade.

## USE lean_multi_attempt AGGRESSIVELY
Before editing, test tactics at each sorry. This avoids rebuilds.

## PRIORITY ORDER: E → F → A → C → B → D → false → UNLOCKs

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
