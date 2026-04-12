# proof — THROW/LIST + BREAK/CONTINUE DECOMPOSED CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T11:05
- **BUILD FIXED** by supervisor (24 compilation errors in noCallFrameReturn area resolved).
- ANF sorry count expanded: break/continue decomposed from 2 monolithic sorries to ~18 per-case sorries.
- **ALL LINE NUMBERS SHIFTED** ~+280 from last prompt. Always verify with `lean_goal` before editing.

## P0: THROW/LIST AREA (3 remaining sorries — L16381, L16430, L16542)

Previous throw/list sorries were reduced from 6 to 3. Verify exact lines with `lean_goal`.

- **L16381**: list case — funcIdx and envPtr evaluated, args list has throw
- **L16430**: list case — funcIdx and envPtr evaluated, args list has throw
- **L16542**: list case — first non-value prop in props has throw

Pattern for all three:
1. HasThrowInHeadList/Props gives the first non-value element with throw
2. Use `Flat_step?_*` context lemmas to step the inner element
3. Apply IH on that element

### EXECUTION:
1. `lean_goal` at L16381 to see the proof state
2. Search: `lean_hover_info` on nearby Flat_step? lemmas
3. Prove L16542 first (props — likely simplest), then L16381, L16430

## P1: BREAK COMPOUND CASES (5 list sorries — L29443-L29447)

These are NEWLY DECOMPOSED from a single monolithic sorry. Each is a specific HasBreakInHead sub-case:

- **L29443**: call_args — list stepping through args
- **L29444**: newObj_args — list stepping through args
- **L29445**: makeEnv_values — list stepping
- **L29446**: objectLit_props — list stepping
- **L29447**: arrayLit_elems — list stepping

All follow the SAME pattern: stepping through a list context. These are likely closable with the same infrastructure as the throw/list cases (P0). Try `lean_multi_attempt` with:
```
["exact Flat_step?_list_ctx h_sub", "apply step_list_compound h_sub", "sorry"]
```

## P2: CONTINUE COMPOUND CASES (13 sorries — L29648-L29660)

Also NEWLY DECOMPOSED. Two groups:

**Second-operand (8)**: L29648-L29655 — needs `trivialChain` for the first operand
**List cases (5)**: L29656-L29660 — same pattern as P1

For the second-operand cases (seq_right, binary_rhs, setProp_val, etc.):
- The first operand is a value (already evaluated)
- Need to show Flat.step? steps through the compound context
- Check for `Flat_step?_*_step` lemmas with the right constructor

## P3: COMPOUND AWAIT/YIELD/RETURN (5 sorries — L24308, L24481, L24537, L24541, L24542)
- Blocked by Flat.step? error propagation — SKIP unless P0-P2 are done

## P4: WHILE CONDITION (2 sorries — L24632, L24644)
## P5: IF-BRANCH K-MISMATCH (2 sorries — L25369, L25409)
## P6: TRYCATCH (3 sorries — L26250, L26268, L26271)

## BLOCKED (12): L11366-L11737 — DO NOT TOUCH

## WASMSPEC-OWNED: L19022, L29822, L29823 — DO NOT TOUCH

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
