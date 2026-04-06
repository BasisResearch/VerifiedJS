# proof — 25 provable ANF sorries in YOUR zones. Close them.

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~3GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13355-13367 and L14263-14275 zones (if_branch individual cases)
- **YOU** own everything else
- DO NOT touch those lines

## L9585 CATCH-ALL: DECOMPOSED! Well done! 5 first-position proved!

The catch-all is now 13 individual sorry cases at L9584-9709.

## ===== PRIORITY 0: SECOND-POSITION CASES (L9584-9709) =====

These 8 cases need a value from the first sub-expression. Use `lean_goal` at each line to see what's in scope.

### seq_right (L9584):
```lean
    | seq_right h_right =>
      rename_i a b
      -- a must be a value (seq evaluates left first). Check lean_goal for h_aval or similar.
      -- Use Steps_seq_ctx_b like seq_left but on right sub-expression
      sorry
```
Use `lean_goal` at L9584 to find how `a` being a value is available. Then apply IH on `b` with Steps_seq_ctx_b.

### binary_rhs (L9585):
The left operand is already a value. Use `lean_goal` to find the hypothesis. Apply IH on rhs, lift with Steps_binary_rhs_ctx_b.

### setProp_val (L9608):
Object is a value. Use Steps_setProp_val_ctx_b.

### getIndex_idx (L9631):
Object is a value. Use Steps_getIndex_idx_ctx_b.

### setIndex_idx (L9655), setIndex_val (L9656):
Previous positions are values. Use Steps_setIndex_idx_ctx_b, Steps_setIndex_val_ctx_b.

### call_env (L9680):
func is a value. Use Steps_call_env_ctx_b.

### newObj_env (L9705):
func is a value. Use Steps_newObj_env_ctx_b.

### APPROACH for each:
1. `lean_goal` at the sorry line
2. Identify value hypothesis for the first sub-expression
3. Apply IH on the stepping sub-expression
4. Lift with the corresponding Steps_*_ctx_b helper
5. Wire VarFreeIn cases (look at how nearby proved cases handle this)
6. `lean_multi_attempt` to test

## ===== PRIORITY 1: LIST CASES (LEAVE AS SORRY) =====
call_args (L9681), newObj_args (L9706), makeEnv_values (L9707), objectLit_props (L9708), arrayLit_elems (L9709) — these need list decomposition helpers that jsspec is building. Skip for now.

## ===== PRIORITY 2: COMPOUND CASES (L10956-L11611) =====
After finishing P0, work on:
- L10956: throw compound HasThrowInHead
- L11107, L11284, L11442: inner_val/inner_arg
- L11113, L11290, L11448: return/await/yield compound
- L11504, L11508, L11509: return/yield/compound
- L11599, L11611: while condition

These need eval context stepping through compound expressions. The normalizeExpr_labeled_branch_step and normalizeExpr_if_branch_step infrastructure already exists — adapt it.

## DO NOT TOUCH (blocked or wasmspec-owned):
- L13355-13367, L14263-14275 (wasmspec — if_branch individual cases)
- L15116, L15134, L15137 (tryCatch — blocked)
- L16220, L16231 (call frame — blocked)
- L16451, L16504 (break/continue — blocked)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
