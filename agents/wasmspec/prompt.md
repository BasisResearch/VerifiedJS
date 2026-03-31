# wasmspec — Close CC value sub-cases (share with jsspec)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! ABSOLUTE RULE: NEVER USE WHILE/UNTIL LOOPS !!
**YOU HAVE WASTED 40+ HOURS STUCK IN WHILE LOOPS. YOUR LAST 4 SESSIONS DID ZERO WORK.**

The pattern `while pgrep -f "lake build"` is an INFINITE LOOP because pgrep matches
YOUR OWN SHELL COMMAND (which contains "lake build" in the string).

### RULES — VIOLATION MEANS ANOTHER WASTED SESSION:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING
2. **NEVER write `until`** — same problem
3. **NEVER write `sleep` inside any loop**
4. `lake serve` is PERMANENT. `pgrep -x lake` will ALWAYS return 0.
5. To build: just run `lake build VerifiedJS.Proofs.ClosureConvertCorrect` directly
6. If build fails: ONE `sleep 60`, then retry ONCE. If fails again, skip.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE (07:00): CC has 20 sorry-grep-hits, build PASSES. File is ~6460 lines.

## FIRST ACTION: Check what jsspec already closed
```bash
grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
Then pick up whatever jsspec DIDN'T finish from the target list below.

## SORRY MAP (as of 07:00 — line numbers WILL shift if jsspec edits):
```
L1520  forIn stub (SKIP)
L1521  forOf stub (SKIP)
L2035  Flat_step?_call_arg_step helper (may be closed by jsspec)
L2048  Flat_step?_call_nonclosure helper (may be closed by jsspec)
L2960  HeapInj refactor staging (SKIP)
L3279  CCStateAgree if-then (SKIP — blocked)
L3301  CCStateAgree if-else x2 (SKIP — blocked)
L3803  call all-values ← TARGET
L3805  call non-value arg ← TARGET
L3806  newObj ← TARGET
L4374  getIndex string value mismatch (SKIP — Flat/Core mismatch)
L4546  setIndex value sub-case ← TARGET
L4868  objectLit all-values ← TARGET (EASIEST)
L5051  arrayLit all-values ← TARGET
L5229  functionDef ← TARGET
L5319  tryCatch ← TARGET (hardest)
L5350  CCState threading while_ (SKIP — blocked)
```

### YOUR TARGETS (pick up whatever jsspec didn't finish):
1. **objectLit all-values** (EASIEST)
2. **arrayLit all-values** (same pattern)
3. **setIndex value sub-case**
4. **call helper lemmas** (L2035, L2048)
5. **call all-values / non-value arg** (L3803, L3805)
6. **newObj** (L3806)
7. **functionDef** (L5229)
8. **tryCatch** (L5319, hardest)

### PROOF PATTERN (from getProp value case ~L3919):
```lean
have hlit : obj = .lit cv := by
  cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
subst hlit
simp [Flat.convertExpr] at hfexpr hst
have hsf_eta : sf = { sf with expr := ... } := by cases sf; simp_all
```

### HOW TO CLOSE L2035 (Flat_step?_call_arg_step):
```lean
simp [Flat.step?, hvals, hfnv, hss, Flat.pushTrace]
```

### HOW TO CLOSE L2048 (Flat_step?_call_nonclosure non-closure cases):
```lean
simp [Flat.step?, hvals, Flat.pushTrace]
```

### WORKFLOW:
1. `grep -n sorry` to find current locations (they shift!)
2. `lean_goal` at target line (LSP takes ~3 min, just WAIT)
3. Study nearby proved cases for patterns
4. Build after each change
5. Move to next target

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns
- forIn/forOf stubs (L1520-1521) — unprovable
- CCState sorries (L3279, L3301, L5350) — architecturally blocked
- getIndex string mismatch (L4374) — Flat/Core semantic mismatch

## CRITICAL: LOG YOUR WORK
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`

## TARGET: Close at least 2 value sub-cases → reduce CC sorry count
