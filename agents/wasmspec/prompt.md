# wasmspec — Close CC value sub-cases (share with jsspec)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! ABSOLUTE RULE: NEVER USE WHILE/UNTIL LOOPS !!
**YOU HAVE WASTED 40+ HOURS STUCK IN WHILE LOOPS. YOUR LAST 3 SESSIONS DID ZERO WORK.**

The pattern `while pgrep -f "lake build"` is an INFINITE LOOP because pgrep matches
YOUR OWN SHELL COMMAND (which contains "lake build" in the string).

### RULES — VIOLATION MEANS ANOTHER WASTED SESSION:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING
2. **NEVER write `until`** — same problem
3. **NEVER write `sleep` inside any loop**
4. `lake serve` is PERMANENT. `pgrep -x lake` will ALWAYS return 0.
5. To build: just run `lake build VerifiedJS.Proofs.ClosureConvertCorrect` directly
6. If build fails: ONE `sleep 60`, then retry ONCE. If fails again, skip.

## MEMORY: 7.7GB total, NO swap.

## STATE (06:05): CC has 17 sorries, build PASSES. File is 6464 lines.

## FIRST ACTION: Check what jsspec closed
```bash
grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean
```

## SORRY MAP (as of 06:05 — line numbers may shift if jsspec edits):
```
L1520  forIn stub (SKIP)
L1521  forOf stub (SKIP)
L2960  HeapInj refactor staging (SKIP)
L3279  CCStateAgree if-then (SKIP — blocked)
L3301  CCStateAgree if-else x2 (SKIP — blocked)
L3807  call callee-is-value ← TARGET
L3918  newObj ← TARGET
L4486  getIndex string value mismatch (SKIP — Flat/Core mismatch)
L4658  setIndex value sub-case ← TARGET
L4980  objectLit all-values ← TARGET (EASIEST)
L5163  arrayLit all-values ← TARGET
L5341  functionDef ← TARGET
L5431  tryCatch ← TARGET (hardest)
L5462  CCState threading while_ (SKIP — blocked)
```

### YOUR TARGETS (pick up whatever jsspec didn't finish):
1. **L4980 — objectLit all-values** (EASIEST)
2. **L5163 — arrayLit all-values** (same pattern)
3. **L4658 — setIndex value sub-case**
4. **L3807 — call callee-is-value**
5. **L3918 — newObj**
6. **L5341 — functionDef**
7. **L5431 — tryCatch** (hardest)

### PROOF PATTERN (from getProp value case ~L3919):
```lean
have hlit : obj = .lit cv := by
  cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
subst hlit
simp [Flat.convertExpr] at hfexpr hst
have hsf_eta : sf = { sf with expr := ... } := by cases sf; simp_all
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
- CCState sorries (L3279, L3301, L5462) — architecturally blocked
- getIndex string mismatch (L4486) — Flat/Core semantic mismatch

## TARGET: Close at least 2 value sub-cases → CC down from wherever jsspec left it
