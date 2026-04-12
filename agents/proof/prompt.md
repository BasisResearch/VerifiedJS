# proof — LIST THROW + COMPOUND AWAIT/YIELD

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T09:05
- ANF: **22** real sorries. CC: 8. Total: **30**.
- GREAT PROGRESS: -12 from last supervisor run (42→30).
- L18325 (HasNonCallFrameTryCatch) is GONE — wasmspec closed it.
- Compound throw catch-all P0 is DECOMPOSED into individual cases. 4 list-throw sorries remain.

## P0: LIST THROW CASES (4 sorries — L16095, L16097, L16099, L16101)

These are the remaining throw-in-head cases for list/args positions:
1. **L16095**: `newObj_args` — f has no throw, but args list does. `hf` is false, need to handle env + args.
2. **L16097**: `makeEnv_values` — throw in first non-value element of values list
3. **L16099**: `objectLit_props` — throw in first non-value prop
4. **L16101**: `arrayLit_elems` — throw in first non-value element

For L16097-16101, the pattern is:
- HasThrowInHeadList/Props gives you the first non-value element with throw
- Split the list at that element: `values = prefix ++ [elem] ++ suffix` where prefix is all values
- Flat.step? steps `elem` through the compound context
- Use `step?_makeEnv_values_ctx` / `step?_objectLit_props_ctx` / `step?_arrayLit_elems_ctx`
- Apply IH on the inner element

For L16095, f and env are values (literals), so step? goes into the args list. Same pattern as list cases but inside `newObj`.

### EXECUTION:
1. Check `lean_hover_info` on `step?_makeEnv_values_ctx` (or similar name) to find the right ctx lemma
2. If ctx lemmas don't exist yet, check what `Flat.step?` does for makeEnv with a list — it should step the first non-value element
3. Prove L16097 first (simplest list case), then replicate for L16099, L16101, L16095

## P1: COMPOUND AWAIT/YIELD (2 sorries — L23768, L23941)

These use the SAME error-propagation pattern as the compound throw cases. Since you proved the throw compound cases, the await/yield compound cases should follow the same structure:
- `normalizeExpr_await_compound_case` / `normalizeExpr_yield_some_compound_case` exist
- The `| _ =>` catch-all needs the same decomposition as throw

## P2-P5 (remaining 7 sorries):
- **P2** (2): L24092, L24104 — while condition
- **P3** (2): L24829, L24869 — if-branch K-mismatch
- **P4** (2): L25710, L25728 — tryCatch body
- **P5** (2): L27278, L27349 — break/continue compound (error propagation)

## BLOCKED (9): L11366-L11643 — trivial mismatch area. DO NOT TOUCH.

## FULL SORRY MAP (22 total):
- **BLOCKED (9)**: L11366, L11414, L11462, L11512, L11539, L11589, L11591, L11641, L11643
- **P0 (4)**: L16095, L16097, L16099, L16101 (list throw) ← YOU ARE HERE
- **P1 (2)**: L23768, L23941 (compound await/yield)
- **P2 (2)**: L24092, L24104 (while condition)
- **P3 (2)**: L24829, L24869 (if-branch K-mismatch)
- **P4 (2)**: L25710, L25728 (tryCatch body)
- **P5 (2)**: L27278, L27349 (break/continue compound)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
