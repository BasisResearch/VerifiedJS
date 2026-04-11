# proof — CLOSE LABELED LIST TAIL + BREAK/CONTINUE NON-HEAD

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T22:05
- ANF: 32 real sorries. CC: 12. Total: **44** (was 50 → -6 this cycle).
- You closed 5 HasReturnInHead list cases last run. EXCELLENT.
- **P0 labeled list tail (L11345, L11377, L11408) has been untouched for 2 runs.** DO THIS FIRST.

## P0: LABELED LIST TAIL CASES (3 sorries, HIGHEST PRIORITY)

Lines L11345, L11377, L11408. These have been P0 for 2 runs without progress. **This is your #1 task.**

Each sorry says "first element has no labeled: requires stepping + list recursion".

Context: We have `HasLabeledInHeadList (e :: rest)` but `¬HasLabeledInHead e`. So the label is somewhere in `rest`. The element `e` needs to step to a value (multi-step), then the list evaluation proceeds to `rest`.

### Approach — use the SAME pattern you used for HasReturnInHead list cases:
1. `lean_goal` at L11345 to see the exact goal state
2. Check: is there a `HasLabeledInHeadList` with head/tail constructors? Use `lean_local_search "HasLabeledInHeadList"`
3. Case split on `h_list`:
   - `head h_e => exact absurd h_e h_e_no`
   - `tail _ h_rest =>` — now need: a step on the list that evaluates `e`
4. If `e` is not a value: use IH on `e` (it has smaller depth), get steps, lift through list context (Steps_makeEnv_values_ctx or similar)
5. If `e` IS a value: list evaluation skips to `rest` immediately

### Helper lemmas you may need (check if they exist):
- `Steps_makeEnv_values_ctx_b` — you already used this at L11330
- Similar for `Steps_objectLit_props_ctx_b`, `Steps_arrayLit_elems_ctx_b`
- A lemma that when first element is a value, list eval proceeds to rest

**Expected: -3 sorries.**

## P1: BREAK/CONTINUE NON-HEAD LIST CASES (2 sorries)

Lines L5005, L6143. Both have the same pattern:
```
| .makeEnv_values _ | .objectLit_props _ | .arrayLit_elems _ => sorry
```

These are non-head-position cases in `HasBreakInHead_step?_produces_error` (L5005) and `HasContinueInHead_step?_produces_error` (L6143).

### Approach:
1. `lean_goal` at L5005 to see what's needed
2. For non-head list cases: the break/continue is in a list element. When that element is in evaluation position, it steps to an error. The list context propagates the error.
3. This follows the same "first non-value element" pattern as the labeled list cases
4. If there's a helper lemma like `step?_list_error_propagation`, use it
5. Otherwise, the step? function should directly compute to an error step

**Expected: -2 sorries.**

## P2: TRIVIAL MISMATCH + CALL_ARGS/NEWOBJ_ARGS LABELED (3 sorries)

- L11260: `¬HasLabeledInHead funcE` — "blocked by trivial mismatch (ANF trivial ≠ flat value)". Check if this can now be closed with existing lemmas.
- L11262: `call_args` labeled in args list — similar to P0 but for the args list in call
- L11314: `newObj_args` labeled in args list — similar to P0 but for newObj

**Expected: -1 to -3 sorries.**

## DO NOT WORK ON:
- L11037-L11210 (trivialChain zone — LSP timeout)
- L16691 (wasmspec owns this — HasNonCallFrameTryCatch)
- L21989+ (compound cases — all blocked)
- ClosureConvertCorrect.lean

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — P0 labeled list tail + P1 break/continue non-head" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
