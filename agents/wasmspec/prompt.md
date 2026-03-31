# wasmspec — Close CC value sub-cases (share with jsspec)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! ABSOLUTE RULE: NEVER USE WHILE/UNTIL LOOPS !!
**YOU HAVE WASTED 39+ HOURS STUCK IN WHILE LOOPS. YOUR LAST 3 SESSIONS DID ZERO WORK.**

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

## STATE: CC has 17 sorries, build PASSES

## CHECK WHAT jsspec HAS DONE FIRST
jsspec has been redirected to your value sub-cases while you were stuck.
Run: `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -25`
See which of your targets jsspec already closed.

### YOUR TARGETS (pick up whatever jsspec didn't finish):
1. **L4831 — objectLit all-values** (EASIEST)
2. **L5014 — arrayLit all-values**
3. **L4509 — setIndex value sub-case**
4. **L3768 — call callee-is-value**
5. **L3769 — newObj**
6. **L5192 — functionDef**
7. **L5282 — tryCatch** (hardest)

Line numbers may have shifted. Use grep to find current locations.

### PROOF PATTERN (from getProp value case ~L3776):
```lean
have hlit : obj = .lit cv := by
  cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
subst hlit
simp [Flat.convertExpr] at hfexpr hst
have hsf_eta : sf = { sf with expr := ... } := by cases sf; simp_all
```

### WORKFLOW:
1. `grep -n sorry` to find current locations
2. `lean_goal` at target line (LSP takes ~3 min, just WAIT)
3. Study nearby proved cases for patterns
4. Build after each change
5. Move to next target

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns
- forIn/forOf stubs — unprovable
- CCState sorries (L2933, L3252, L3274, L5313) — architecturally blocked

## TARGET: Close at least 2 value sub-cases → CC down from wherever jsspec left it
