# Sorry Report (Wed Mar 25 11:12:55 AM UTC 2026)

- [ ] `VerifiedJS/Proofs/LowerCorrect.lean:69` — `theorem lower_behavioral_correct` — `obtain ⟨ir, hirsteps, hrel⟩ := lower_sim_steps s t h _ _ _ _ (IR.LowerSimRel.init s t h (by sorry)) hsteps`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:106` — `theorem anfConvert_step_star` — `sorry`
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:1177` — `theorem anfConvert_halt_star_aux` — `sorry`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1101` — `theorem closureConvert_step_simulation` — `sorry`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1870` — `theorem closureConvert_step_simulation` — `| call _ _ => sorry -- needs env/heap/funcs correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:1871` — `theorem closureConvert_step_simulation` — `| newObj _ _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3520` — `def hst3_def` — `| objectLit _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3521` — `def hst3_def` — `| arrayLit _ => sorry -- needs env/heap correspondence`
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:3522` — `def hst3_def` — `| functionDef _ _ _ _ _ => sorry -- needs env/heap/funcs + CC state`
- [ ] `VerifiedJS/Wasm/Semantics.lean:257` — `theorem readLE?_none_of_size_zero` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:5857` — `def LowerRel` — `showing the target takes a matching step. These are`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6095` — `theorem init` — `Each case is decomposed below; each sub-case may still be`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6204` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6212` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6216` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6219` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6222` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6225` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6266` — `theorem step_sim` — `| some t => sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6269` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6272` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6275` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6278` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:6281` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:7929` — `theorem step_sim` — `| .i64 => sorry -- i64 load: needs EmitCodeCorr.load_i64 constructor`
- [ ] `VerifiedJS/Wasm/Semantics.lean:7932` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:7935` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8376` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8379` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8616` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8619` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8726` — `theorem step_sim` — `sorry`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8885` — `theorem ir_forward_sim` — `exact LowerSimRel.init prog irmod hlower (by sorry)`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8900` — `theorem ir_stutter_sim` — `exact LowerSimRel.init prog irmod hlower (by sorry)`
- [ ] `VerifiedJS/Wasm/Semantics.lean:8924` — `theorem lower_behavioral_obs_correct` — `(LowerSimRel.init prog irmod hlower (by sorry))`

**Total: 35 sorries**
