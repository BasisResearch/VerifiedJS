# proof — Close compound + while + tryCatch sorries in ANFConvertCorrect.lean

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~3.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13976+ and L15210+ zones (if_branch individual cases)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own everything else in ANFConvertCorrect.lean
- DO NOT touch wasmspec or jsspec zones

## STATUS: Rate limits blocked all agents for 18 hours. Fresh start.

## Current ANF sorry count: 53 (down from 55 on Apr 6)

## ===== P0: THE COMPOUND SORRY AT L11713 =====

Line 11713: `sorry -- compound HasThrowInHead cases: need eval context stepping through seq/let/call/etc.`

This is the REMAINING compound case after `normalizeExpr_throw_compound_case` handles the direct constructor cases (L11707). The `| _` catch-all at L11711 catches cases where `HasThrowInHead` is in a deeper eval context position (e.g., `seq_left`, `let_init`, etc.).

**Approach**: Use `lean_goal` at L11713 to see the exact proof state. Then:
1. Case-split on the remaining HasThrowInHead constructors
2. For each case (seq_left, let_init, assign_val, etc.): the throw is in a sub-expression. The sub-expression steps first in the eval context, producing the throw, which then propagates.
3. Use `normalizeExpr_throw_compound_case` recursively via depth induction if needed, OR use `lean_multi_attempt` to try `simp`/`omega`/`exact`/`apply` on each sub-case.

## ===== P1: REMAINING COMPOUND SORRIES (L11864, L11870, L12041, L12047, L12199, L12205) =====

These follow the same pattern for return/await/yield:
- L11864: `| _ => sorry -- compound inner_val: seq, let, assign, if, call, throw, etc.`
- L11870: `sorry -- compound HasReturnInHead cases`
- L12041: `| _ => sorry -- compound inner_arg`
- L12047: `sorry -- compound HasAwaitInHead cases`
- L12199: `| _ => sorry -- compound inner_val`
- L12205: `sorry -- compound HasYieldInHead cases`

Once you solve L11713, apply the same pattern to these.

## ===== P2: STRUCTURAL SORRIES (L12261, L12265, L12266) =====

```
L12261: | some val => sorry -- return (some val): compound, can produce .let
L12265: | some val => sorry -- yield (some val): compound, can produce .let
L12266: | _ => sorry -- compound expressions: needs structural induction
```

These are in `anfConvert_step_star`. Use `lean_goal` to understand the exact state.

## ===== P3: WHILE + TRYCATCH + CALLFRAME + BREAK (8 sorries) =====

```
L12356: sorry -- While condition value case
L12368: sorry -- Condition-steps case
L16366: sorry -- tryCatch body-error
L16384: sorry -- tryCatch body-step
L16387: | _ => sorry -- compound cases
L17470: sorry -- noCallFrameReturn
L17481: sorry -- body_sim IH
L17701: sorry -- break
L17754: sorry -- continue
```

## WORKFLOW
1. Start with `lean_goal` at L11713 to see the exact proof state
2. Try `lean_multi_attempt` with candidate tactics
3. If a tactic works, edit the file to replace the sorry
4. Verify with `lean_diagnostic_messages` after editing
5. Move to next sorry

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
