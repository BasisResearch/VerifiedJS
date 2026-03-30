# jsspec — ANF DECOMPOSITION IS YOUR #1 PRIORITY

## STATUS
- CC: 22 sorries. Proof agent active, closing value sub-cases. You help with helpers.
- ANF: 17 sorries — ALL blocked on monolithic `anfConvert_step_star`. DECOMPOSE IT.
- Wasm: 16 sorries (wasmspec owns). DO NOT touch Semantics.lean.

## YOUR MISSION: DECOMPOSE ANF sorries

The 17 ANF sorries are all inside one giant sorry. This has been stuck for 5+ DAYS.
Break it into per-constructor cases NOW.

### P0: ANF per-constructor stepping lemmas — TOP PRIORITY
Read `VerifiedJS/Proofs/ANFConvertCorrect.lean` lines 3368-3426 (the sorry sites).
For EACH ANF.Expr constructor:
1. `lean_goal` at the sorry
2. Write a per-constructor proof attempt in `.lake/_tmp_fix/anf_<constructor>.lean`
3. Even 15 new inner sorries (one per constructor) is BETTER than 1 monolithic sorry
4. Use `lean_multi_attempt` on each case

Target constructors (easiest first):
- litValue, litClosure (should be trivial — already done in main file?)
- trivial (Expr.trivial already handled)
- throw, return — simple control flow
- let, seq — need multi-step induction
- if, while — need branch analysis

### P1: Verify staged files still compile
Check these in `.lake/_tmp_fix/`:
- `cc_state_mono.lean` (CCState monotonicity)
- `cc_objectLit_ccstate.lean` (objectLit CCState)
- `cc_convertExpr_not_lit_v2.lean` (convertExpr_not_lit)
- `cc_exprAddrWF_propagate.lean` (ExprAddrWF)

For each: `lean .lake/_tmp_fix/<file>` — if it compiles, write EXACT edit instructions for proof agent.

### P2: Integration instructions
For every staged file that compiles clean, post in your log:
```
INTEGRATION: <filename>
OLD: <exact old_string to match>
NEW: <exact new_string replacement>
```
So the proof agent can apply them directly.

## WORKFLOW
1. Read the relevant definitions first (`lean_hover_info`, `lean_local_search`)
2. Write standalone `.lean` files in `.lake/_tmp_fix/`
3. Test with `lean_run_code` or `lean_verify`
4. LOG every 30 min to agents/jsspec/log.md

## CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- DO NOT run `lake build` (wastes time, proof agent is building)
