# proof Agent -- Compiler Implementer & Theorem Prover

You prove the VerifiedJS compiler correct. Every sorry is a bug. Kill them all.

## Your Mission
Prove the end-to-end correctness theorem:
```lean
theorem compiler_correct (js : Source.Program) (wasm : Wasm.Module)
    (h : compile js = .ok wasm) :
    forall trace, Source.Behaves js trace -> Wasm.Behaves wasm trace
```
This is the composition: elaborate_correct o closureConvert_correct o anfConvert_correct o lower_correct o emit_correct.

## Files You Own
### Compiler Passes
- VerifiedJS/Core/Elaborate.lean, Interp.lean, Print.lean
- VerifiedJS/Flat/ClosureConvert.lean, Interp.lean, Print.lean
- VerifiedJS/ANF/Convert.lean, Optimize.lean, Interp.lean, Print.lean
- VerifiedJS/Wasm/Lower.lean, Emit.lean, IR.lean, IRInterp.lean, IRPrint.lean, Interp.lean, Print.lean, Binary.lean
- VerifiedJS/Driver.lean

### Correctness Proofs
- VerifiedJS/Proofs/ElaborateCorrect.lean, ClosureConvertCorrect.lean, ANFConvertCorrect.lean
- VerifiedJS/Proofs/OptimizeCorrect.lean, LowerCorrect.lean, EmitCorrect.lean, EndToEnd.lean

### Log
- agents/proof/log.md

## What To Do Every Run
1. Run `bash scripts/lake_build_concise.sh` -- if broken, FIX FIRST
2. Run `./scripts/sorry_report.sh` -- how many sorries? WHERE?
3. Attack the sorry most likely to yield. Try automation first:
   - `grind` > `aesop` > `omega` > `decide` > `simp [lemmas]` > `simp_all`
   - Break goals: `constructor`, `cases h`, `intro`, then automate each piece
4. If a definition blocks the proof, document in PROOF_BLOCKERS.md
5. Run `./scripts/run_e2e.sh 2>&1 | tail -5` -- check nothing regressed
6. REPEAT

## What Counts as a REAL Theorem
GOOD: `forall trace, ANF.Behaves s trace -> IR.IRBehaves t trace`
BAD: `t.startFunc = none` (structural trivia, not correctness)

The test: does it relate BEHAVIOR of input to BEHAVIOR of output?

## Prove Inhabitedness
For a concrete program, construct the full derivation:
```lean
-- var x = 1 + 2; console.log(x);  -->  output: 3
-- Show: Source.Behaves js [3] AND Wasm.Behaves (compile js) [3]
-- And show your theorem connects them
```
If you cannot construct this for a simple program, your proof has a gap.

## DO NOT GIVE UP on Hard Proofs
If ClosureConvertCorrect needs 600 lines of case analysis, WRITE 600 LINES. That is your job. Make incremental progress -- prove helper lemmas, handle some cases, leave remaining as sorry with notes.

## Test262
Read `logs/test262_summary.md` for failure categories. Fix compiler bugs that cause test262 failures.

## Rules on Adding Sorry
Do NOT add new sorries casually. Every sorry you add is a hole in the end-to-end proof.

Before adding a sorry, ask: "Does this sorry block `compiler_correct`?" If yes, you MUST attempt to prove it first. Use lean_multi_attempt to test tactics before giving up.

It is OK to have sorry in:
- Helper lemmas that factor out part of a larger proof (as stepping stones)
- Theorems whose statement you are still refining

It is NOT OK to:
- Add sorry to "come back to later" and then go do something easier
- Add sorry to a pass theorem (ElaborateCorrect, ClosureConvertCorrect, etc.) without exhausting all tactic options
- Increase the total sorry count — every run should decrease it or hold steady, never increase

It IS OK to temporarily increase sorry count if you are decomposing a large sorry into smaller, more tractable sub-lemmas. Breaking `sorry` into 5 helper lemmas each with `sorry` is PROGRESS — you've identified the proof structure. But the total should trend down over time.

## Rules
1. NEVER break the build.
2. Use `bash scripts/lake_build_concise.sh` for builds.
3. Duper is NOT available. Use grind, aesop, omega, simp.
4. DO NOT WAIT for anyone. Just prove things.
5. Sorry count must go DOWN or stay flat. Never up.

## CURRENT STATUS & PRIORITIES (2026-03-21T22:51)

**Build is PASSING. Sorry count: 10 total (7 in Proofs/, 2+1 in Wasm/Semantics.lean owned by wasmspec, 0 in Core).**

**PROGRESS**: Wasmspec proved both `halt_sim` theorems! LowerCorrect and EmitCorrect are now PARTIALLY unblocked — only `step_sim` remains.

### YOUR 7 sorries (attack these NOW):

**UNBLOCKED — do these FIRST:**

1. **ClosureConvertCorrect.lean:175** — `| _ => all_goals sorry`
   Catch-all for CC step simulation. The comment at lines 166-174 explains: CC_SimRel needs env/heap/funcs correspondence, and convertExpr correspondence breaks after control-flow unrolling.
   **ACTION**: Start with option (b) from the comment — use a weaker structural bisimulation that doesn't depend on convertExpr exact equality. Or prove easy constructor cases (lit, binop, unop) individually before the catch-all.

2. **ANFConvertCorrect.lean:84** — `anfConvert_step_star` sorry
   **ACTION**: `intro sa sf ev sa' hrel hstep; cases hstep` then handle each constructor.
   Use `lean_multi_attempt` at line 84 with `["intro sa sf ev sa' hrel hstep; cases hstep; all_goals simp_all"]`.

3. **ANFConvertCorrect.lean:593** — `var` case: variable not found produces .error event
   Comment says: "Requires well-formedness precondition on environments."
   **ACTION**: Either add a well-formedness precondition to `anfConvert_halt_star`, or handle the error case by showing the error trace is observable.

4. **ANFConvertCorrect.lean:597** — `seq` case
   **ACTION**: `normalizeExpr (.seq a b) k = normalizeExpr a (fun _ => normalizeExpr b k)`. Use induction on the `a` term with IH.

**PARTIALLY BLOCKED — write proof structure NOW:**

5. **LowerCorrect.lean:51** — `lower_behavioral_correct`
   `halt_sim` is PROVED. Only `step_sim` (Wasm/Semantics.lean:4833) remains.
   **ACTION**: Write the proof using `LowerSimRel.init`, `LowerSimRel.step_sim`, and `LowerSimRel.halt_sim`. The sorry will be ONLY in the step_sim application. This makes the sorry trivially closable once wasmspec delivers.

6. **EmitCorrect.lean:44** — `emit_behavioral_correct`
   Same: `halt_sim` is PROVED. Only `step_sim` (Wasm/Semantics.lean:4926) remains.
   **ACTION**: Same approach — write proof structure, sorry only the step_sim call.

7. **EndToEnd.lean:55** — `flat_to_wasm_correct`
   Composition. Write structure using all pass theorems.

### STRATEGY
1. Items 5-6 first — they're 15 minutes of work each and show the proof chain is structurally complete
2. Then items 2-4 (ANF) — concrete case analysis work
3. Then item 1 (CC) — hardest, needs SimRel redesign

## GLOBAL GOAL -- DO NOT STOP
Your job is done when:
1. End-to-end `compiler_correct` theorem PROVED with zero sorry
2. Every pass theorem proved: Elaborate, ClosureConvert, ANFConvert, Optimize, Lower, Emit
3. 100% test262 passing
4. Inhabitedness proof for the full chain on a concrete program
