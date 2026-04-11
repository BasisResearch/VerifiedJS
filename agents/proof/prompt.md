# proof — CLOSE LIST CASES + LABELED LIST TAIL CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T21:05
- ANF: ~38 real sorries. CC: 12. Total: ~50.
- HasNonCallFrameTryCatchInHead defined at L9489. Good.
- makeEnv_values head case proved (L11200-L11247). Good.
- objectLit_props head case proved (L11249-L11279). Good.
- arrayLit_elems head case proved (L11281-L11310). Good.
- **3 new labeled list tail sorries** at L11248, L11280, L11311 — these need list recursion.
- **4 HasReturnInHead list sorries**: L19085, L19394, L19552, L19553.

## P0: LABELED LIST TAIL CASES (3 sorries, MOST TRACTABLE)

Lines L11248, L11280, L11311 all say "first element has no labeled: requires stepping + list recursion".

### What these sorries need:
When `HasLabeledInHeadList (e :: rest)` but `¬HasLabeledInHead e`, then `HasLabeledInHeadList rest`.
The first element `e` is NOT the one with the labeled. So:
1. `e` must be evaluated to a value (since it's first in evaluation order)
2. After `e` becomes a value, the list shifts and the labeled element is now closer to head
3. Need: a step that evaluates `e` in the list context, preserving the list structure

### Strategy:
```
-- For each (makeEnv_values, objectLit_props, arrayLit_elems):
-- h_e_no : ¬HasLabeledInHead e
-- h_list : HasLabeledInHeadList (e :: rest)  or similar
-- By cases on h_list:
--   | head h_e => exact absurd h_e h_e_no
--   | tail _ h_rest => -- now HasLabeledInHeadList rest
--     -- Need to show e steps to a value, then recurse on rest
--     -- This requires: e is not a value (otherwise list would skip it)
--     -- OR: if e IS a value, the list evaluation moves to rest immediately
```

Check: does `HasLabeledInHeadList` have `head` and `tail` constructors? Use `lean_hover_info` at L11248 on the sorry to see the goal, then `lean_local_search "HasLabeledInHeadList"`.

### Expected: -3 sorries if all 3 tail cases close.

## P1: HasReturnInHead LIST CASES (4 sorries)

Lines:
```
L19085: | call_args h_a => sorry -- list: return in args of call f env args
L19394: | newObj_args h_a => sorry -- list: return in args of newObj
L19552: | objectLit_props h_a => sorry -- list: return in props of objectLit
L19553: | arrayLit_elems h_a => sorry -- list: return in elems of arrayLit
```

These are harder. Same pattern as P0 but in the HasReturnInHead context.
- `h_a : HasReturnInHeadList args` (or HasReturnInHeadProps)
- Need to find which element has HasReturnInHead
- Need step through list context (call_args_ctx, newObj_args_ctx, etc.)

### Strategy:
1. First check if P0's approach works here too
2. Use `lean_local_search "HasReturnInHeadList"` to find helpers
3. Try `call_args` (L19085) first since it matches the labeled list pattern

### Expected: -1 to -4 sorries.

## DO NOT WORK ON:
- L10940-L11217 (trivialChain zone — LSP timeout)
- L15421, L15441, L15469 (wasmspec owns these — HasNonCallFrameTryCatch helpers)
- L19909, L20082 (await/yield compound — blocked)
- L20138-L20143 (return/yield .let compound — blocked)
- L20233-L20245 (while — blocked)
- L20970-L21010 (if_branch — blocked by K-mismatch)
- L21851-L21872 (tryCatch — blocked)
- L23199-L23500 (end-of-file — blocked)
- ClosureConvertCorrect.lean

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — P0 labeled list tail + P1 HasReturn list" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
