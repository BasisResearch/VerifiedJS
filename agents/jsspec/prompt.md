# jsspec — CC HELPER LEMMAS + ANF STAGING

## STATUS
- Wasm sorries: ALL architecturally blocked. Cannot write Semantics.lean. STOP trying Wasm.
- CC: 22 sorries (grep -c). Proof agent closing value sub-cases. YOU help by staging helper lemmas it needs.
- ANF: 17 sorries, all need induction on depth. Stage proofs.

## YOUR MISSION: Stage CC helper lemmas in `.lake/_tmp_fix/`

The proof agent is BLOCKED on several CC sorries because helper lemmas don't exist yet.
Write self-contained helper lemma files that the proof agent can integrate.

### P0: convertExpr_not_lit — DONE (staged in cc_convertExpr_not_lit_v2.lean)
Good work. This unblocks L2133 + L2243.

### P1: ExprAddrWF propagation — DONE (staged in cc_exprAddrWF_propagate.lean)
Good work. This unblocks L4056 + L4154.

### P2: ANF per-constructor stepping lemmas — IN PROGRESS
The 17 ANF sorries all need `anfConvert_step_star` decomposed per constructor.
Read VerifiedJS/Proofs/ANFConvertCorrect.lean lines 3368-3426 to see the sorry sites.
For EACH constructor (letBinding, sequence, conditional, etc.):
- `lean_goal` at the sorry
- Stage a proof attempt in `.lake/_tmp_fix/anf_<constructor>.lean`
- Even partial proofs (with inner sorries) help

### P3: CCState monotonicity lemma — REPORTEDLY DONE (staged in cc_state_mono.lean)
You said it compiles clean. VERIFY it still works:
```bash
lean .lake/_tmp_fix/cc_state_mono.lean
```
If verified, tell proof agent how to integrate it. This unblocks L2646, L2668, L4103, L4405.

### P4: objectLit CCState — REPORTEDLY STAGED (cc_objectLit_ccstate.lean)
You staged this last session. VERIFY it compiles. If so, provide exact integration instructions for proof agent to apply at L4103.

### P5: INTEGRATE staged files into main codebase
You have MULTIPLE completed staged files. The biggest impact right now is getting them integrated:
1. Read each staged file in `.lake/_tmp_fix/`
2. For each one that compiles clean, write the EXACT edit (old_string → new_string) the proof agent needs to apply
3. Post these as integration instructions in your log

**THIS IS YOUR HIGHEST PRIORITY.** Staged files sitting unintegrated are WASTED WORK.

### WORKFLOW
1. Read the relevant definitions first (`lean_hover_info`, `lean_local_search`)
2. Write standalone `.lean` files in `.lake/_tmp_fix/`
3. Test with `lean_run_code` or `lean_verify`
4. LOG every 30 min to agents/jsspec/log.md

### CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- DO NOT run `lake build` (wastes time, proof agent is building)
