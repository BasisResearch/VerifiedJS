# Sorry Report (Wed Mar 25 06:12:31 PM UTC 2026)

- [ ] `VerifiedJS/Proofs/LowerCorrect.lean:69` — `theorem lower_behavioral_correct` — `obtain ⟨ir, hirsteps, hrel⟩ := lower_sim_steps s t h _ _ _ _ (IR.LowerSimRel.init s t h (by sorry)) hsteps`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:106` — `theorem anfConvert_step_star` — `sorry`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:1365` — `lemma (induction` — `sorry`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:829` — `theorem false` — `| forIn => sorry /- forIn converts to .lit .undefined (stub); theorem false -/`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:830` — `theorem false` — `| forOf => sorry /- forOf converts to .lit .undefined (stub); theorem false -/`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1113` — `theorem closureConvert_step_simulation` — `sorry`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1897` — `theorem closureConvert_step_simulation` — `| call _ _ => sorry -- needs env/heap/funcs correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1898` — `theorem closureConvert_step_simulation` — `| newObj _ _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3547` — `def hst3_def` — `| objectLit _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3548` — `def hst3_def` — `| arrayLit _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3549` — `def hst3_def` — `| functionDef _ _ _ _ _ => sorry -- needs env/heap/funcs + CC state`
- [ ] `VerifiedJS/Wasm/Semantics.lean:5885` — `def LowerRel` — `showing the target takes a matching step. These are`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6123` — `theorem init` — `Each case is decomposed below; each sub-case may still be`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6232` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6240` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6244` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6247` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6250` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6253` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6294` — `theorem step_sim` — `| some t => sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6297` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6300` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6303` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6306` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6309` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:7974` — `theorem step_sim` — `| .i64 => sorry -- i64 load: needs EmitCodeCorr.load_i64 constructor`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8232` — `theorem step_sim` — `| .i64 => sorry -- i64 store: needs EmitCodeCorr.store_i64 constructor`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8796` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8799` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9036` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9039` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9146` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9305` — `theorem ir_forward_sim` — `exact LowerSimRel.init prog irmod hlower (by sorry)`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9320` — `theorem ir_stutter_sim` — `exact LowerSimRel.init prog irmod hlower (by sorry)`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9344` — `theorem lower_behavioral_obs_correct` — `(LowerSimRel.init prog irmod hlower (by sorry))`

**Total: 35 sorries**
