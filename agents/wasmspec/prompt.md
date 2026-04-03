# wasmspec — Investigate FuncsCorr + HasBreakInHead/HasContinueInHead patterns

## EXCELLENT WORK on the CCStateAgree analysis! jsspec is implementing your fix.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec is implementing CCStateAgree fix
- **DO NOT** edit ANFConvertCorrect.lean — proof agent owns it
- **DO NOT** run `lake build` anything
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.

## YOUR JOB: Two investigations

### Investigation 1: FuncsCorr (blocks L4271 — non-consoleLog call)

The CC sorry at L4271 is blocked by missing `FuncsCorr` — a correspondence between `sf.funcs[idx]` and `sc.funcs[idx]`. This would unblock the general function call case.

Tasks:
1. Search for `FuncsCorr` in ClosureConvertCorrect.lean — does it exist? Is it defined but unused?
2. Search for `sf.funcs` and `sc.funcs` usage patterns
3. Look at how `Flat.convertExpr` handles `.call` — specifically how func indices relate
4. Determine: is FuncsCorr a simple index-mapping invariant? Can it be added to the simulation relation?
5. Write findings to `agents/wasmspec/funcscorr_analysis.md`

### Investigation 2: HasBreakInHead / HasContinueInHead flat stepping

The proof agent needs to prove `hasBreakInHead_flat_error_steps` (ANF L6650) and `hasContinueInHead_flat_error_steps` (L6663). These say: if an expression has a break/continue at its evaluation head, it flat-steps to `.lit .undefined` with an error trace.

Tasks:
1. Find the definitions of `HasBreakInHead` and `HasContinueInHead` — what are their constructors?
2. For each constructor, trace what `Flat.step?` does:
   - `.break label` → what does Flat.step? return?
   - `.seq (break label) rest` → Flat.step? steps `.seq`, how?
   - `.return (some (break label))` → etc.
3. Determine if induction on `HasBreakInHead` straightforwardly produces flat error steps
4. Write findings to `agents/wasmspec/break_continue_analysis.md`

### Step 1: Log start
```bash
echo "### $(date -Iseconds) Starting FuncsCorr + break/continue analysis" >> agents/wasmspec/log.md
```

### Step 2: Do both investigations (FuncsCorr first, then break/continue)

### Step 3: Log and EXIT
```bash
echo "### $(date -Iseconds) Run complete — [summary]" >> agents/wasmspec/log.md
```

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
