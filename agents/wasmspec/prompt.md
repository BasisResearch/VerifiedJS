# wasmspec — FIX if_step_sim ERRORS (unblocks ALL downstream LSP verification)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3GB available right now (supervisor freed memory).
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## CRITICAL: normalizeExpr_if_step_sim has 12 ERRORS (L9285-L9399) that block ALL downstream LSP

These errors prevent LSP verification of hasAbruptCompletion, NoNestedAbrupt, tryCatch, and ALL other sorries after L9285. FIXING THESE IS YOUR #1 PRIORITY.

### Error Pattern 1: `env.lookup` vs `ANF.Env.lookup` (L9285, L9308, L9356, L9380)

The proof does:
```lean
have hlookup : env.lookup name_c = some v := by
  simp only [ANF.evalTrivial] at heval; split at heval <;> simp_all
```
But `env : Flat.Env` (from destructuring `sf`), so `env.lookup` resolves to `List.lookup`. The hypothesis after simp becomes `ANF.Env.lookup env name_c = some v`.

**FIX**: Check if `ANF.Env.lookup` is just `List.lookup` (use `lean_hover_info`). If yes, try:
```lean
have hlookup : env.lookup name_c = some v := by
  simp only [ANF.evalTrivial] at heval
  split at heval <;> simp_all [ANF.Env.lookup]
```
Or try `exact heval` or `assumption` if they're definitionally equal. Or change the goal to `ANF.Env.lookup env name_c = some v`.

### Error Pattern 2: `Unknown identifier 'Flat.pushTrace'` (L9292, L9315, L9364, L9388)

`Flat.pushTrace` is `private` in Flat/Semantics.lean. It can't be referenced outside.

**FIX OPTIONS** (pick one):
A. Make `pushTrace` public: In `VerifiedJS/Flat/Semantics.lean` L191, change `private def pushTrace` to `def pushTrace`
B. Replace `Flat.pushTrace {...} .silent` with an explicit state literal `{ expr := ..., env := ..., ... }`
C. Use `step?_pushTrace_expand` simp lemma instead

**Option A is simplest** — just remove `private` from L191.

### Error Pattern 3: `simp at this` no progress (L9298, L9321, L9370, L9394)

After `have := Flat.step?_if_true ...`, the `simp at this` fails. The goal involves `step?_pushTrace_expand` on a pushTrace result.

**FIX**: Try `simp [Flat.step?_pushTrace_expand] at this` directly, or inline the pushTrace expansion.

### Error Pattern 4: `observableTrace` mismatch (L9303, L9326, L9375, L9399)

`htrace : observableTrace sa_trace = observableTrace trace` but goal needs matching with `[.silent, .silent]` vs `[.silent]`. The issue is the proof claims 2 silent steps but the trace arithmetic doesn't work out.

**FIX**: The `by simp [observableTrace_append, observableTrace]; exact htrace` pattern may need `observableTrace_silent` or manual `List.filter` reasoning. Check what `observableTrace` does with `.silent` events.

## PRIORITY ORDER
1. Fix `private pushTrace` (Option A — remove `private` from Flat/Semantics.lean L191)
2. Fix `env.lookup` issues (check type aliases, add simp lemma or exact)
3. Fix `simp` progress issues
4. Fix `observableTrace` trace issues
5. Once all 12 errors are fixed, the LSP will verify all theorems after L9285 → sorry count may drop

## AFTER FIXING ERRORS: Work on let/while step_sim sorries
- L9045: let step sim
- L9135, L9147: while step sim

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
