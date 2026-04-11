# jsspec — ARCHITECTURAL FIX: CCStateAgree via Path A

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T16:05
- CC: 12 real sorries. Total: 58 (ANF 46 + CC 12).
- **YOU CLOSED 3 Or.inr SORRIES!** CC went from 15 → 12. GREAT WORK. File grew by 428 lines.
- No quick Or.inr wins remain. The remaining 12 CC sorries are all architecturally blocked.

## REMAINING CC SORRY CLASSIFICATION (12 total):
1. **Multi-step simulation gap** (3): L5475, L6572, L6780/L6791
   - L5475: captured var (.getEnv takes 2 Flat steps vs 1 Core step)
   - L6572: non-consoleLog function call (Flat call is N steps vs Core's 1)
   - L6780/L6791: same class as L5475
2. **CCStateAgree** (5): L5923, L5949, L8835, L8912, L9028
   - L5923: if-true — st' includes else_ conversion state
   - L5949: if-false — needs CCStateAgree for input
   - L8835: tryCatch with CCStateAgree gap
   - L8912: CCStateAgree after inner conversion
   - L9028: while_ lowers to if/seq/while pattern
3. **CCStateAgree + tryCatch finally** (1): L8838
4. **Axiom/semantic mismatch** (1): L7431 (getIndex string)
5. **FuncsCorr/functionDef** (1): L8678

## YOUR MISSION: Fix CCStateAgree (5 sorries → 0)

### WARNING: Monotone approach was REJECTED on 2026-03-31
"Weakening output to ≤ breaks ~10 sub-stepping chaining cases that feed equality into `convertExpr_state_determined`."
**DO NOT** try simple monotone weakening.

### Path A: Position-based naming (HIGHEST IMPACT)
Make `convertExpr` state-independent for variable naming by using **position-based names** in `freshVar` instead of a global `nextId` counter.

#### Investigation steps (DO THIS FIRST):
1. Read `freshVar` in `Flat/ClosureConvert.lean` — current implementation
2. Read `CCState` definition — what fields?
3. Read `CCStateAgree` definition — what does it require?
4. Count callers of `freshVar` — scope the change
5. Check if `convertExpr` threads CCState ONLY for `freshVar`, or also for func table

#### If freshVar is the ONLY reason for state threading:
- Change `freshVar` to use position encoding instead of counter
- `CCStateAgree` becomes trivially true
- **This eliminates 5+ sorries at once**

#### If CCState also tracks func table:
- Keep func table threading, but make variable naming position-based
- `CCStateAgree` only needs to track func table (simpler)

### Path B (fallback): Lazy conversion
Instead of converting both branches eagerly, change `convertExpr` for if/while to only convert the taken branch. More invasive but eliminates the root cause.

### DO THIS RUN:
1. Read `Flat/ClosureConvert.lean` — find `freshVar`, `CCState`, `convertExpr`
2. Assess Path A feasibility: how many callers, how many lines change?
3. If Path A looks feasible (< 200 lines changed in ClosureConvert.lean), START implementing
4. Report findings even if you can't finish

## DO NOT ATTEMPT:
- Multi-step simulation sorries (L5475, L6572, L6780, L6791) — needs framework redesign
- L7431 — semantic mismatch axiom
- L8678 — functionDef needs multi-step + FuncsCorr

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgree Path A investigation" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
