# jsspec — ARCHITECTURAL FIX: CCStateAgree

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
2. **Or.inr structural mismatch** (3 sorries: L5270, L5414, L5701): Flat drops outer wrapper on error, Core keeps it. Neither `Or.inl` nor `Or.inr` works.
3. **Multi-step simulation** (4 sorries: L5049, L6144, L6352, L6363): Core compound op = 1 step, Flat = N steps.
4. **Unprovable** (1: L7003) + **HeapInj/finally** (2: L8250, L8410)

## YOUR MISSION: Fix CCStateAgree (5 sorries → 0)

CCStateAgree is the single biggest blocker (5 sorries). The problem:
- `convertExpr` produces a new CC state after converting BOTH branches
- But at runtime, only one branch executes
- The IH provides `CCStateAgree` for the state AFTER the taken branch
- We need `CCStateAgree` for the state AFTER both branches (the "join" state)

### Approach 1: Monotonic state + weakening lemma
If CC state only grows (fresh name counter increases, no deletions), then:
- State after branch1 ≤ state after both branches
- Any `CCStateAgree` for a sub-state should lift to a super-state
- Prove: `CCStateAgree st_sub st → st_sub.counter ≤ st.counter → CCStateAgree st st`

### Investigation steps:
1. `lean_hover_info` on `CCStateAgree` to get its definition
2. Read the definition. Is it a simple counter comparison? Or does it track more?
3. `lean_local_search "CCStateAgree"` — find all existing lemmas
4. `lean_local_search "convertExpr_state_mono"` — does state monotonicity exist?
5. Read 30 lines around L5496 to understand the exact gap

### Approach 2: Change simulation relation
Instead of requiring exact `CCStateAgree st_after_both`, weaken the post-condition to `CCStateAgree st_after_taken_branch`. This requires changing the theorem statement — check if downstream consumers can tolerate this.

### Approach 3: Lazy conversion
Convert branches lazily (only the taken branch). This requires changing `convertExpr` — MORE INVASIVE but correct.

### DO THIS FIRST:
1. Understand CCStateAgree's definition
2. Check if `convertExpr_state_mono` exists
3. Try Approach 1 — it's the least invasive

## DO NOT ATTEMPT:
- Or.inr sorries — deeper architectural issue
- Multi-step simulation — needs framework redesign
- L7003 — unprovable

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgree architectural fix investigation" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
