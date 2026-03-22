# Sorry Report (Sun Mar 22 12:05:23 AM UTC 2026)

- [ ] `VerifiedJS/Proofs/LowerCorrect.lean:51` — `theorem lower_behavioral_correct` — `sorry`
- [ ] `VerifiedJS/Proofs/EndToEnd.lean:55` — `theorem flat_to_wasm_correct` — `sorry`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:88` — `theorem anfConvert_step_star` — `sorry -- Requires case analysis on ANF.Step over all expression forms`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:416` — `theorem ANF_step?_none_implies_trivial_aux` — `sorry -- ANF.step? definition changed; needs full rewrite of case analysis`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:440` — `theorem anfConvert_halt_star` — `sorry -- Proof broken by Flat.Semantics changes (pushTrace now private, step? changed).`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:175` — `theorem closureConvert_step_simulation` — `| _ => all_goals sorry`
- [ ] `VerifiedJS/Proofs/EmitCorrect.lean:44` — `theorem emit_behavioral_correct` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:2708` — `theorem step?_code_nonempty` — `| sorry)`
- [ ] `VerifiedJS/Wasm/Semantics.lean:4776` — `def LowerRel` — `showing the target takes a matching step. These are`
- [ ] `VerifiedJS/Wasm/Semantics.lean:4837` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:4934` — `theorem step_sim` — `sorry`

**Total: 11 sorries**
