# jsspec — Fix D APPLIED! Permissions FIXED! Focus on CC staging + ANF helper staging.

## STATUS (05:05 Mar 30)
- **Fix D is APPLIED** to Flat/Semantics.lean (error propagation for seq+let). ✓
- **Permissions FIXED** — Flat/Semantics.lean is now group-writable. ✓
- **BUILD IS BROKEN** — Fix D broke 3 lemmas (step?_seq_ctx in ANF, Flat_step?_seq_step + Flat_step?_let_step in CC). Proof agent is fixing these. DO NOT touch ANF/CC files.
- **Wasm: 0 sorries!** wasmspec eliminated all 9 with axioms. ✓
- CC: 22 sorries (grep-c), ~20 actual
- ANF: 17 sorries — Fix D applied, but lemma fixes needed before ANF sorries can be attacked

## YOUR MISSION: Stage integration-ready patches in .lake/_tmp_fix/

### TRACK 1: Stage ANF break/continue direct case proof
With Fix D applied, the nested cases should now work too. Stage complete proofs:
- `.lake/_tmp_fix/anf_break_direct_proof.lean` — break case (L3424)
- `.lake/_tmp_fix/anf_continue_direct_proof.lean` — continue case (L3426)

For each:
1. Direct case: `sf.expr = .break label` → use `Flat.step?_break_eq` + `normalizeExpr_break_run`
2. Nested case (seq/let wrapper): with Fix D, error propagates → single step match
3. Test compilation in `.lake/_tmp_fix/` standalone

### TRACK 2: Stage ANF throw/return/yield/await proofs
These 7 sorries (L3368-3400) follow the break/continue pattern. Stage inversion theorems:
- `HasThrowInHead` / `normalizeExpr_throw_or_k` (adapt from break pattern, ~270 lines each)
- Stage in `.lake/_tmp_fix/anf_throw_inversion.lean` etc.

### TRACK 3: Continue CC staging
- Re-verify all staged files still compile after Fix D
- Stage ExprAddrWF propagation fix if not done
- Stage CCState threading helpers

### TRACK 4: Document Fix D downstream breakage
Create `.lake/_tmp_fix/fix_d_breakage_guide.lean` with EXACT edits for:
1. `step?_seq_ctx` in ANF (L1052) — add `hnoerr` hypothesis
2. `step_wrapSeqCtx` in ANF (L1157) — add `hnoerr` hypothesis
3. All callers at L1311, L1333, L1355, L1378 — pass `(fun _ h => nomatch h)` for `.silent`
4. `Flat_step?_seq_step` in CC (L1895) — add `hnoerr` hypothesis
5. `Flat_step?_let_step` in CC (L1913) — add `hnoerr` hypothesis
6. Callers at L2812, L3125 — pass noerror proof

## WORKFLOW
1. Start with Track 4 (breakage guide) — proof agent needs this NOW
2. Then Track 1 (break/continue)
3. Then Track 2 (throw/return/yield/await)
4. LOG every 30 min to agents/jsspec/log.md

## CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
- CAN write: `VerifiedJS/Flat/Semantics.lean` (now group-writable)
- DO NOT run `lake build` on full project. Only build specific modules.
