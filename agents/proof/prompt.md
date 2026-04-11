# proof — CLOSE NoNestedAbrupt_step_preserved (L15893)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- hasAbruptCompletion_step_preserved: **PROVED** (great work!)
- NoNestedAbrupt_step_preserved (L15893): still `sorry`, with commented-out proof L15894+
- ANF: 32 real sorries. CC: 87 (72 are FuncsCorr, jsspec will bulk-close). Total: 119.

## P0: UNCOMMENT NoNestedAbrupt_step_preserved (L15893)

YOU JUST DID THIS EXACT PATTERN for hasAbruptCompletion_step_preserved. Do it again.

The sorry at L15893 has a commented-out proof immediately below it (L15894+).

**EXACT STEPS:**
1. Delete the `sorry -- TODO: fix for error propagation; cases need split at hstep for match t with` at L15893
2. Uncomment the proof block below: change `/-obtain` to `obtain` and remove the closing `-/`
3. The proof will have errors because step? now has THREE branches (error event, non-error step, none) instead of TWO

**For each `split at hstep` that breaks:**
The error branch is NEW. You handled this in hasAbruptCompletion. For NoNestedAbrupt, the error branch is:
```lean
· -- error event: produces .lit .undefined, which satisfies NoNestedAbrupt.lit
  split at hstep <;> (obtain ⟨_, rfl⟩ := hstep; simp [Flat.pushTrace]; exact .lit)
```

**ALSO ADD** termination hint:
```lean
termination_by Flat.Expr.depth e
decreasing_by all_goals (simp_all [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth]; omega)
```

**EXPECTED RESULT**: -1 sorry (L15893 closed).

## P1: AFTER P0 — L16819 and L16890

These are at the end of anfConvert_step_star. Run `lean_goal` at each. They may require NoNestedAbrupt_step_preserved which you just proved.

## P2: L16589 (noCallFrameReturn)

Read the comment at L16589-16599. Need `catchParam ≠ "__call_frame_return__"`. Check if `by decide` or `by simp` works.

## SKIP: trivial mismatch (L10183-10554), if_branch (L14519/14559), compound error prop (wasmspec owns), CC file

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — NoNestedAbrupt L15893" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
