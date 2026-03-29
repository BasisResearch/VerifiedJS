# jsspec — CC HELPER LEMMAS + ANF STAGING

## STATUS
- Wasm sorries: ALL architecturally blocked (your analysis confirmed). Cannot write Semantics.lean. STOP trying Wasm.
- CC: 23 sorries. Proof agent closing value sub-cases. YOU help by staging helper lemmas it needs.
- ANF: 17 sorries, all need induction on depth. Stage proofs.

## YOUR MISSION: Stage CC helper lemmas in `.lake/_tmp_fix/`

The proof agent is BLOCKED on several CC sorries because helper lemmas don't exist yet.
Write self-contained helper lemma files that the proof agent can integrate.

### P0: convertExpr_not_lit (HIGHEST VALUE — unblocks L2133 + L2243)
These sorries need a lemma: for stub constructors (forIn, forOf, generator),
`Flat.convertExpr e st ≠ (.lit _, _)`. Specifically:
```lean
theorem convertExpr_not_forIn (args : List Core.Expr) (st : Flat.CCState) :
  ¬ ∃ l st', Flat.convertExpr (.forIn args) st = (.lit l, st')
```
Same for forOf, generator. Stage in `.lake/_tmp_fix/cc_convertExpr_not_lit_v2.lean`.

### P1: ExprAddrWF propagation (unblocks L3868 + L3966)
Need: if `ExprAddrWF (.objectLit props) = True` then each element satisfies ExprAddrWF.
```lean
theorem ExprAddrWF_objectLit_propagate (props : List (String × Core.Expr)) :
  ExprAddrWF (.objectLit props) = true → ∀ p ∈ props, ExprAddrWF p.2 = true
```
Same for arrayLit. Stage in `.lake/_tmp_fix/cc_exprAddrWF_propagate.lean`.

### P2: ANF per-constructor stepping lemmas (stage for future ANF work)
The 17 ANF sorries all need `anfConvert_step_star` decomposed per constructor.
Read VerifiedJS/Proofs/ANFConvertCorrect.lean lines 3368-3426 to see the sorry sites.
For EACH constructor (letBinding, sequence, conditional, etc.):
- `lean_goal` at the sorry
- Stage a proof attempt in `.lake/_tmp_fix/anf_<constructor>.lean`
- Even partial proofs (with inner sorries) help

### WORKFLOW
1. Read the relevant definitions first (`lean_hover_info`, `lean_local_search`)
2. Write standalone `.lean` files in `.lake/_tmp_fix/`
3. Test with `lean_run_code` or `lean_verify`
4. LOG every 30 min to agents/jsspec/log.md

### CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- DO NOT run `lake build` (wastes time, proof agent is building)
