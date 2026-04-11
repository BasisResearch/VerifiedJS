# proof — UNCOMMENT NoNestedAbrupt_step_preserved (L14639)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- hasAbruptCompletion_step_preserved: **PROVED** at L14178 (confirmed working).
- NoNestedAbrupt_step_preserved (L14639): still `sorry`, with commented-out proof L14640-15020+.
- ANF: 34 real sorries. CC: 15. Total: 49.
- **wasmspec just closed 6 sorries** — compound inner depth cases all resolved.

## P0: UNCOMMENT NoNestedAbrupt_step_preserved (L14639)

The sorry at L14639 has a commented-out proof immediately below it (L14640+). This proof was working before Flat.step? error propagation changes.

**EXACT STEPS:**
1. Delete the `sorry -- TODO: fix for error propagation; cases need split at hstep for match t with` at L14639
2. Uncomment the proof block below: change `/-obtain` to `obtain` and remove the closing `-/`
3. The proof will have errors because step? now has THREE branches (error event, non-error step, none) instead of TWO

**For each `split at hstep` that breaks:**
The error branch is NEW. You already handled this pattern in hasAbruptCompletion_step_preserved. For NoNestedAbrupt, the error branch should be:
```lean
· -- error event: produces .lit .undefined, which satisfies NoNestedAbrupt.lit
  split at hstep <;> (obtain ⟨_, rfl⟩ := hstep; simp [Flat.pushTrace]; exact .lit)
```

**ALSO ADD** termination hint (same as hasAbruptCompletion):
```lean
termination_by Flat.Expr.depth e
decreasing_by all_goals (simp_all [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth]; omega)
```

**EXPECTED RESULT**: -1 sorry (L14639 closed). May cascade to simplify L15565/L15636.

## P1: AFTER P0 — CHECK COMPOUND BREAK/CONTINUE CASES

After NoNestedAbrupt_step_preserved is proved:
- L15565 and L15636 are break/continue "Category B" compound cases
- They need error propagation through compound Flat.step? — the SAME pattern wasmspec used for inner depth cases
- Check if `normalizeExpr_labeled_or_k` + Steps_ctx_lift can close them
- Run `lean_goal` at L15565 to see what's needed

## P2: L15335 (noCallFrameReturn) — QUICK WIN?

L15335 needs `catchParam ≠ "__call_frame_return__"`. Check if `noCallFrameReturn_tryCatch_direct_bridge` (L4137) can close it directly.

## SKIP: trivial mismatch (L10183-10554), if_branch (L13273/13313), anfConvert_step_star, CC file

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — NoNestedAbrupt L14639" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
