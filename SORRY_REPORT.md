# Sorry Report (Wed Mar 25 09:17:40 PM UTC 2026)

- [ ] `VerifiedJS/Proofs/LowerCorrect.lean:69` — `theorem lower_behavioral_correct` — `obtain ⟨ir, hirsteps, hrel⟩ := lower_sim_steps s t h _ _ _ _ (IR.LowerSimRel.init s t h (by sorry)) hsteps`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:106` — `theorem anfConvert_step_star` — `sorry`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:1499` — `theorem anfConvert_halt_star_aux` — `sorry`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:829` — `theorem false` — `| forIn => sorry /- forIn converts to .lit .undefined (stub); theorem false -/`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:830` — `theorem false` — `| forOf => sorry /- forOf converts to .lit .undefined (stub); theorem false -/`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1113` — `theorem closureConvert_step_simulation` — `sorry`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1897` — `theorem closureConvert_step_simulation` — `| call _ _ => sorry -- needs env/heap/funcs correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1898` — `theorem closureConvert_step_simulation` — `| newObj _ _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3547` — `def hst3_def` — `| objectLit _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3548` — `def hst3_def` — `| arrayLit _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3549` — `def hst3_def` — `| functionDef _ _ _ _ _ => sorry -- needs env/heap/funcs + CC state`
- [ ] `VerifiedJS/Wasm/Semantics.lean:5914` — `def LowerRel` — `showing the target takes a matching step. These are`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6152` — `theorem init` — `Each case is decomposed below; each sub-case may still be`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6261` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6269` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6273` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6276` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6279` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6282` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6323` — `theorem step_sim` — `| some t => sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6326` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6329` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6332` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6335` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6338` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9148` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9151` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9394` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9397` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9628` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9813` — `theorem ir_forward_sim` — `exact LowerSimRel.init prog irmod hlower (by sorry)`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9828` — `theorem ir_stutter_sim` — `exact LowerSimRel.init prog irmod hlower (by sorry)`
- [ ] `VerifiedJS/Wasm/Semantics.lean:9852` — `theorem lower_behavioral_obs_correct` — `(LowerSimRel.init prog irmod hlower (by sorry))`

**Total: 33 sorries**
