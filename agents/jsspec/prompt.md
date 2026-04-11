# jsspec — ARCHITECTURAL FIX: CCStateAgree via Path A

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T15:30
- CC: 15 real sorries. Total: 60.
- **ALL 15 CC sorries are architecturally blocked.** You confirmed this last 4 runs.
- No quick wins remain. The ONLY way forward is architectural fixes.

## ROOT CAUSES (your analysis)
1. **CCStateAgree** (5 sorries: L5496, L5522, L8407, L8484, L8600): convertExpr converts BOTH branches of if/while, but execution only takes one, leaving state gap.
2. **Or.inr structural mismatch** (3 sorries: L5270, L5414, L5701): Flat drops outer wrapper on error, Core keeps it.
3. **Multi-step simulation** (4 sorries: L5049, L6144, L6352, L6363): Core compound op = 1 step, Flat = N steps.
4. **Unprovable** (1: L7003) + **HeapInj/finally** (2: L8250, L8410)

## YOUR MISSION: Fix CCStateAgree (5 sorries → 0)

### WARNING: Monotone approach was REJECTED on 2026-03-31
From PROOF_BLOCKERS.md: "weakening output to ≤ breaks ~10 sub-stepping chaining cases that feed equality into `convertExpr_state_determined`."
**DO NOT** try simple monotone weakening. It was already attempted and failed.

### Path A: Position-based naming (from PROOF_BLOCKERS.md)
Make `convertExpr` state-independent by using **position-based naming** in `freshVar` instead of a global `nextId` counter. This eliminates `CCStateAgree` entirely.

#### How it works:
1. Currently `freshVar` increments `nextId` counter → different branches get different `nextId` states
2. Change: instead of `nextId`, use a position encoding (e.g., path from root: "if_true_0", "if_false_0") to generate unique names
3. This makes `convertExpr` a PURE function of the expression (no state threading for fresh names)
4. `CCStateAgree` becomes trivial or unnecessary

#### Investigation steps:
1. Read `freshVar` definition in `Flat/ClosureConvert.lean` — how does it work now?
2. Read `CCState` definition — what fields does it have?
3. Read `CCStateAgree` definition — what does it require?
4. Count how many callers of `freshVar` exist — scope the change
5. Check if `convertExpr` threads CCState only for `freshVar`, or also for other purposes (e.g., func table)

#### If freshVar is the ONLY reason for state threading:
- Change `freshVar` to take a path/position argument instead of state
- Make `convertExpr` stateless for variable naming
- `CCStateAgree` becomes trivially true

#### If CCState also tracks func table:
- Keep func table threading, but make variable naming position-based
- `CCStateAgree` only needs to track func table (simpler)

### Path B (if Path A is too invasive): Change simulation relation
Weaken the post-condition from `CCStateAgree st_after_both` to `CCStateAgree st_after_taken_branch`. Check if `convertExpr_state_determined` can tolerate this weakening.

### DO THIS RUN:
1. Read `Flat/ClosureConvert.lean` — find `freshVar`, `CCState`, `convertExpr`
2. Assess Path A feasibility: how many lines would change?
3. If Path A looks feasible (< 200 lines changed), START implementing
4. If not, investigate Path B

## DO NOT ATTEMPT:
- Or.inr sorries — deeper architectural issue
- Multi-step simulation — needs framework redesign
- L7003 — unprovable

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgree Path A investigation" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
