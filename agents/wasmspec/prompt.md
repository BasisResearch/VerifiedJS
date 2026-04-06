# wasmspec — Investigate K-mismatch + close provable if_branch cases

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~2.3GB free. USE LSP ONLY — no builds.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L10063-10158 (labeled_branch_step second-position)
- jsspec may work on list cases (L10159, L10183-10187)
- **YOU** own L13697+ and L14792+ ONLY (if_branch zones)

## ===== CRITICAL: K-MISMATCH BLOCKS ¬HasIfInHead SUB-CASES =====

The ¬HasIfInHead sub-cases for second-position constructors (binary_rhs, call_env, etc.) have a **fundamental K-mismatch issue**, same as in labeled_branch_step.

For `normalizeExpr (.binary op lhs rhs) K`: after lhs trivialChain passthrough, K for rhs becomes `fun rhsTriv => bindComplex (.binary op (trivialOfFlat lhs) rhsTriv) K`. After stepping lhs→(.lit v), K becomes `fun rhsTriv => bindComplex (.binary op (trivialOfFlatValue v) rhsTriv) K`. These differ because `trivialOfFlat (.var x) ≠ trivialOfFlatValue v`.

The theorem conclusion needs the SAME body, but body depends on K. **The ¬HasIfInHead sub-cases are UNPROVABLE as stated when the first sub-expression is not already a .lit value.**

## ===== YOUR STRATEGY =====

### P0: Check if second-position constructors are needed in HasIfInHead
1. Check ALL call sites of `normalizeExpr_if_branch_step` and `normalizeExpr_if_branch_step_false`
2. At each call site, determine what HasIfInHead derivation is passed
3. If only first-position constructors are ever used, the second-position cases are DEAD CODE
4. If dead code: remove binary_rhs, call_env, newObj_env, setProp_val, getIndex_idx, setIndex_idx, setIndex_val from HasIfInHead. This removes 14 sorries (7 per theorem).

### P1: Close list cases if helpers exist
The list cases (call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems) may be provable with existing list-based infrastructure:
- `Steps_call_arg_ctx_b`, `Steps_newObj_arg_ctx_b`, `Steps_makeEnv_values_ctx_b`
- `Steps_objectLit_val_ctx_b`, `Steps_arrayLit_elem_ctx_b`

For list cases: the HasIfInHeadList means SOME element has HasIfInHead. Elements before it are trivialChains. The approach:
1. Evaluate preceding elements to values (trivialChain_eval_value)
2. IH on the labeled element
3. Lift through the list context
4. BUT: same K-mismatch may apply for preceding elements!

Check if list cases have the same K issue before investing time.

### P2: If constructors ARE needed, try .lit v sub-case
For each sorry, case-split: if the first sub-expression is already .lit v, the K matches perfectly. This sub-case IS provable. Leave the non-.lit sub-case as sorry.

## YOUR SORRIES (7 second-position + 5 list per theorem):

### normalizeExpr_if_branch_step — around L13697+:
```
Second-position (K-mismatch blocked):
  binary_rhs L13697 · sorry
  call_env L13722 · sorry
  newObj_env L13771 · sorry
  setProp_val L13796 · sorry
  getIndex_idx L13820 · sorry
  setIndex_idx L13845 · sorry
  setIndex_val L13870 · sorry
List-based:
  call_args L13723
  newObj_args L13772
  makeEnv_values L13871
  objectLit_props L13872
  arrayLit_elems L13873
```

### normalizeExpr_if_branch_step_false — around L14792+:
Mirror of above.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
