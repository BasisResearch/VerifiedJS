# wasmspec — FIX if_step_sim ERRORS then close let/while sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.6GB available right now.
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: You split L9093 into sub-cases and added normalizeExpr_while_decomp. Good progress.

## TASK 1: Fix if_step_sim ERRORS at L9285-L9399 (PRIORITY 1)

These 12 errors block ALL downstream LSP verification. There are 4 repeated error patterns across 4 if-condition cases (lit, var, this, compound).

### Error 1: `Flat.pushTrace` is private (L9297, L9320, L9364, L9388)
**FIX**: In `VerifiedJS/Flat/Semantics.lean`, find `private def pushTrace` (around L191) and remove `private`. Make it `protected def pushTrace` or just `def pushTrace`.

### Error 2: `env.lookup` vs `ANF.Env.lookup` (L9290, L9313, L9356, L9380)
After simp, the hypothesis becomes `ANF.Env.lookup env name = some v` but the goal needs `env.lookup name = some v`.
**FIX**: Check with `lean_hover_info` whether `ANF.Env.lookup` and `List.lookup` are the same. If yes, add `[ANF.Env.lookup]` to the simp call. Or use `exact` instead of simp.

### Error 3: `simp at this` no progress (L9299, L9322, L9370, L9394)
The `have := Flat.step?_if_true ...` produces something that `simp` can't simplify.
**FIX**: Try `simp [Flat.step?_pushTrace_expand]` directly, or try `exact this` if the types already match, or `unfold Flat.pushTrace at this`.

### Error 4: `observableTrace` mismatch (L9303, L9326, L9375, L9399)
The trace has `[.silent, .silent]` but needs to match the goal.
**FIX**: Likely just needs `simp [observableTrace_append, observableTrace_silent, observableTrace_nil, List.append_assoc]`.

### Approach: Fix error 1 FIRST (just remove `private`), then build to see how many errors remain.

## TASK 2: Close let step sim (L9050)

Currently: `sorry -- Need characterization of what produces .let, flat simulation`

When ANF has `.let name init body` and `exprValue? init = none`, ANF.step? steps init. The Flat simulation needs to show Flat can match. The normalizeExpr for let should produce something Flat can step.

Use `lean_hover_info` on normalizeExpr and ANF.step? for `.let` to understand the exact structure.

## TASK 3: Continue while sub-cases (L9140, L9152)

You already split L9093 and added `normalizeExpr_while_decomp`. Continue:
- L9140: while condition value case — transient state
- L9152: condition-steps case — needs flat while-condition simulation

## PRIORITY ORDER
1. Fix `private pushTrace` → rebuild → see remaining errors
2. Fix env.lookup, simp, observableTrace errors
3. L9050 (let step sim)
4. L9140, L9152 (while)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
