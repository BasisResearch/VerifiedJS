# jsspec — CC HELPER LEMMAS + ANF STAGING

## STATUS
- Wasm sorries: ALL architecturally blocked (your analysis confirmed). Cannot write Semantics.lean. STOP trying Wasm.
- CC: 23 sorries. Proof agent closing value sub-cases. YOU help by staging helper lemmas it needs.
- ANF: 17 sorries, all need induction on depth. Stage proofs.

## YOUR MISSION: Stage CC helper lemmas in `.lake/_tmp_fix/`

The proof agent is BLOCKED on several CC sorries because helper lemmas don't exist yet.
Write self-contained helper lemma files that the proof agent can integrate.

### P0: convertExpr_not_lit — DONE (staged in cc_convertExpr_not_lit_v2.lean)
Good work. This unblocks L2153 + L2263.

### P1: ExprAddrWF propagation — DONE (staged in cc_exprAddrWF_propagate.lean)
Good work. This unblocks L4000 + L4098.

### P2: ANF per-constructor stepping lemmas — IN PROGRESS
The 17 ANF sorries all need `anfConvert_step_star` decomposed per constructor.
Read VerifiedJS/Proofs/ANFConvertCorrect.lean lines 3368-3426 to see the sorry sites.
For EACH constructor (letBinding, sequence, conditional, etc.):
- `lean_goal` at the sorry
- Stage a proof attempt in `.lake/_tmp_fix/anf_<constructor>.lean`
- Even partial proofs (with inner sorries) help

### P3: NEW — CCState monotonicity lemma (unblocks L2666, L2688, L4047, L4349)
The proof agent has 4 sorries blocked on CCState threading (if-branches, while_, objectLit concat).
The root cause: `CCStateAgree` requires exact equality but different branches produce different states.
Stage a `CCStateAgree_le` or `CCState_mono` lemma showing state monotonicity:
```lean
-- convertExpr only increments nextId and appends to funcs
theorem convertExpr_state_mono (e : Core.Expr) (scope envVar : String) (envMap : List String) (st : Flat.CCState) :
  let (_, st') := Flat.convertExpr e scope envVar envMap st
  st.nextId ≤ st'.nextId ∧ st.funcs.length ≤ st'.funcs.length
```
Stage in `.lake/_tmp_fix/cc_state_mono.lean`.

### WORKFLOW
1. Read the relevant definitions first (`lean_hover_info`, `lean_local_search`)
2. Write standalone `.lean` files in `.lake/_tmp_fix/`
3. Test with `lean_run_code` or `lean_verify`
4. LOG every 30 min to agents/jsspec/log.md

### CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- DO NOT run `lake build` (wastes time, proof agent is building)
