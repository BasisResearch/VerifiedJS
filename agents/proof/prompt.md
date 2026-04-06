# proof — 25 provable ANF sorries in YOUR zones. Close them.

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~6GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13355-13367 and L14263-14275 zones (if_branch individual cases)
- **YOU** own everything else
- DO NOT touch those lines

## L9585 CATCH-ALL: DECOMPOSED! 5 first-position proved!

The catch-all is now 13 individual sorry cases at L9584-9709.

## ===== PRIORITY 0: SECOND-POSITION CASES (8 sorries) =====

These cases have HasLabeledInHead in the SECOND sub-expression. The FIRST sub-expression must evaluate to a value first.

### KEY PATTERN (from if_branch_step L12940-12988):
The if_branch_step theorem already solves this for `HasIfInHead`. YOUR cases use `HasLabeledInHead` — adapt the same pattern:

1. Show the first sub-expression is a `trivialChain` — use `no_if_head_implies_trivial_chain` analog, OR derive from `normalizeExpr_labeled_or_k`:
   - `normalizeExpr (a.seq b) K` produced `.labeled label body`
   - Unfolding: `normalizeExpr a (fun tv => normalizeExpr b K)` produced labeled
   - By `normalizeExpr_labeled_or_k`, either `HasLabeledInHead a label` or continuation produced it
   - Use `normalizeExpr_trivial_implies_chain` to show `a` is trivialChain when it normalizes trivially

2. Use `trivialChain_eval_value` (L11699) to step first sub-expr to a value

3. Lift with `Steps_X_ctx_b`, add one discard step, then apply IH on second sub-expr

### CONCRETE TEMPLATE for seq_right (L9584):
```lean
    | seq_right h_right =>
      rename_i b a  -- NOTE: a=left (first), b=right (has label)
      -- Step 1: show a is trivialChain
      -- normalizeExpr_seq' unfolds seq normalization
      simp only [ANF.normalizeExpr_seq'] at hnorm
      -- a must normalize trivially since label is in b, not a
      -- Use normalizeExpr_trivial_implies_chain or adapt no_if_head_implies_trivial_chain
      sorry -- fill in trivialChain derivation
      -- Step 2: trivialChain_eval_value on a
      -- Step 3: Steps_seq_ctx_b to lift, one discard step, IH on b
```

**LOOK AT L12940-12988** — this is the EXACT same pattern for HasIfInHead in seq. Copy and adapt:
- Replace `HasIfInHead` with `HasLabeledInHead`
- Replace `.if cond then_ else_` with `.labeled label body`
- The rest (trivialChain, Steps_seq_ctx_b, discard step, IH) is identical

### binary_rhs (L9585):
Same pattern. First show `lhs` is trivialChain, eval to value, use `Steps_binary_lhs_ctx_b` to lift, then in the resulting `.binary op (.lit v) rhs`, apply IH on rhs with `Steps_binary_rhs_ctx_b`.

### setProp_val (L9608), getIndex_idx (L9631), setIndex_idx (L9655), setIndex_val (L9656), call_env (L9680), newObj_env (L9705):
All follow the same second-position pattern. First sub-expr → trivialChain → value → lift → IH.

### APPROACH for each:
1. `lean_goal` at the sorry line
2. `simp only [ANF.normalizeExpr] at hnorm` to unfold
3. Derive trivialChain for first sub-expr (see L12941 pattern)
4. `trivialChain_eval_value` to step first sub-expr to value (see L12945)
5. Lift with Steps_*_ctx_b (see L12948)
6. Discard step (see L12954)
7. Derive depth bound for second sub-expr
8. IH application on second sub-expr (see L12958-12961)
9. Wire up final existential (see L12962-12988)

## ===== PRIORITY 1: LIST CASES (LEAVE AS SORRY) =====
call_args (L9681), newObj_args (L9706), makeEnv_values (L9707), objectLit_props (L9708), arrayLit_elems (L9709) — jsspec built the helpers, but list induction is complex. Skip for now.

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
