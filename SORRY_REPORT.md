# Sorry Report (Sat Mar 21 03:05:00 AM UTC 2026)

- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:84` — `anfConvert_step_star` — hardest sorry, needs full case analysis on ANF.Step
- [ ] `VerifiedJS/Proofs/ANFConvertCorrect.lean:127` — `anfConvert_halt_star` — partially done (lit case proven), remaining cases should contradict
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:50` — `closureConvert_step_simulation` — hardest CC sorry, needs Flat.Step case analysis + expr correspondence
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:114` — `step?_none_implies_lit_aux` — partially done (10+ cases proven), remaining compound exprs
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:142` — `closureConvert_halt_preservation` — **GENUINELY FALSE** for forIn (closureConvert stubs as .lit .undefined)
- [ ] `VerifiedJS/Proofs/ClosureConvertCorrect.lean:143` — `closureConvert_halt_preservation` — **GENUINELY FALSE** for forOf (same as forIn)

**Total: 6 sorries** (was 4 — restructuring exposed sub-goals)
**2 of 6 are UNSOUND** — need theorem precondition or closureConvert fix
