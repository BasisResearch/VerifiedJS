# jsspec — CC architectural fixes + ANF second-position cases

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- You MAY also work on ANF second-position cases (see below).

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: CC has 12 sorry tactics, ALL classified as architecturally blocked.

## ===== CC SORRY CLASSIFICATION (from your last run) =====

ALL 12 CC sorries are blocked. You classified them as:
- Multi-step simulation gap: L4905, L6040, L6049
- CCStateAgree: L5237, L5262, L8089, L8092, L8165, L8275
- Missing FuncsCorr: L5829, L7930
- Unprovable: L6688

### P0: CCStateAgree — The Most Common Blocker (6 sorries)

The CCStateAgree problem: when converting `if cond then_ else_`, the discarded branch's conversion changes `nextId`/`funcs.size` in CCState. The proof can't show `CCStateAgree` between the state used and the state produced.

**Possible fix**: Change the simulation relation to allow CCState to diverge on `nextId`/`funcs.size` as long as the important invariants hold. Specifically:

1. `lean_goal` at L5237 to see exactly what CCStateAgree needs
2. `lean_local_search "CCStateAgree"` to find the definition
3. Check if CCStateAgree can be weakened to only require agreement on functionally-relevant fields
4. If so, edit the definition in the appropriate file and fix downstream

**This is high-leverage**: fixing CCStateAgree could unblock 6 of 12 CC sorries.

### P1: FuncsCorr invariant (2 sorries: L5829, L7930)

These need a `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence.
1. `lean_local_search "FuncsCorr"` — does this invariant exist?
2. If not, define it and thread it through the simulation relation
3. L5829 (function call) is the simpler case — start there

### SKIP: Multi-step (L4905, L6040, L6049), Unprovable (L6688)

## ===== SECONDARY: ANF SECOND-POSITION CASES =====

If CC progress is fully blocked, switch to ANF second-position cases.
These are in `normalizeExpr_labeled_step_sim` (L10203-10466):

```
L10203: sorry -- trivialChain passthrough
L10226: setProp_val sorry -- second-position trivial mismatch
L10249: getIndex_idx sorry -- second-position trivial mismatch
L10273: setIndex_idx sorry -- second-position trivial mismatch
L10274: setIndex_val sorry -- second-position trivial mismatch
L10298: call_env sorry -- second-position trivial mismatch
L10347: newObj_env sorry -- second-position trivial mismatch
```

These 7 cases all have the same "trivial mismatch" issue. Use `lean_goal` at L10226 to understand:
- The continuation `k` produces `.trivial t` for trivials, but the expr has the label in a second-position sub-expression
- The trivialChain mechanism handles the first sub-expression but not the second

**Check if you can:**
1. Add a `trivialChain_second_position` helper that handles the second sub-expression
2. Or show the second-position case reduces to something provable

## WORKFLOW
1. Start with CCStateAgree (P0): `lean_goal` at L5237, then `lean_local_search "CCStateAgree"`
2. If CCStateAgree fix is too invasive, try FuncsCorr (P1)
3. If all CC blocked, switch to ANF second-position (L10226)
4. For each sorry: `lean_goal` → `lean_multi_attempt` → edit → `lean_diagnostic_messages`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
