# jsspec — Close real CC sorries (CCState threading + convertExpr_not_lit)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! CRITICAL BUG FROM PREVIOUS SESSIONS !!
Previous agents got PERMANENTLY STUCK in `while` / `until` loops waiting for processes.
**NEVER use `while` or `until` loops. NEVER use `sleep` in a loop.**
`lake serve` processes are PERMANENT. `pgrep -x lake` always returns 0.

### ABSOLUTE RULES:
1. **NEVER use `while` or `until` loops** — not for pgrep, not for anything
2. If a build is running (`pgrep -f "lake build"`): SKIP, do other work, try later
3. Just run your build command directly. If it fails, diagnose and retry once.

## MEMORY: 7.7GB total, NO swap.

## STATE (01:05): CC has 19 grep-sorry, ~16 real sorries

### Remaining sorry breakdown (your targets):
- **2 convertExpr_not_lit** (L2663, L2773): needs helper for 3 stub constructors
- **1 captured variable** (L2857): needs getEnv stepping + EnvCorrInj
- **1 CCState if-true** (L3176): needs restructured st_a choice (current witness is WRONG — st_a' doesn't account for else_ conversion)
- **2 CCState if-false** (L3198): same class as L3176
- **1 CCState while_** (L5237): while_ duplicates sub-expressions

### KEY INSIGHT FOR L3176/L3198 CCStateAgree:
The current witness `st_a = st` doesn't work because `st' = (convertExpr else_ (convertExpr then_ st).snd).snd`
but `st_a' = (convertExpr then_ st).snd` — these DON'T agree (else_ changes the state).

**SOLUTION**: You need to pick `st_a` such that converting then_ from `st_a` produces
an output `st_a'` that agrees with `st'`. Use `convertExpr_state_determined` (L548-552):
if `CCStateAgree st1 st2`, then `convertExpr` from both produces same expr AND output
states that agree. The trick: find an `st_a` where `CCStateAgree st st_a` AND
`(convertExpr then_ st_a).snd` gives you a state whose nextId/funcs.size matches st'.

One approach: restructure the existential witness entirely. Instead of `st_a = st`,
use `st_a` with `nextId = st'.nextId - delta_then` and `funcs.size = st'.funcs.size - delta_then`.
But this requires computing how much then_ adds, which is what convertExpr_state_determined gives you.

ALTERNATIVELY: maybe the theorem statement itself needs strengthening — the CCStateAgree
invariant might need to be `≤` (monotonicity) rather than `=` (equality).

## YOUR TARGETS (5 sorries):

### TARGET 1: L2663 + L2773 (convertExpr_not_lit)
These need a lemma: `convertExpr_not_lit` for the 3 stub constructors (forIn, forOf, and one more).
`lean_goal` at L2663 → understand what's needed → prove or add the helper.

### TARGET 2: L2857 (captured variable)
Goal: When a variable is captured (lookupEnv returns some idx), the Flat expression is
`.getEnv (.var envVar) idx`. Need to show Flat stepping this corresponds to Core stepping `.var name`.
Look at how `.var name` (non-captured, L2858-2908) is proved — adapt for captured case.

### TARGET 3: L3176 + L3198 (CCStateAgree) — HARDEST
See KEY INSIGHT above. May require restructuring the theorem witness.

### TARGET 4: L5237 (while_ CCState threading)
Similar to if: CCState diverges because while_ duplicates sub-expressions.

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf sorries (L1502-1503) — unprovable stubs
- L3692, L3693, L4261, L4433, L4755, L4938, L5116, L5206 — wasmspec owns these

## TARGET: Close at least 2 of your 5 assigned sorries → CC from 19 to ~17
