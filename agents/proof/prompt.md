# proof — Compound cases + K-mismatch redesign investigation

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~800MB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13901+ and L14996+ zones (if_branch individual cases)
- jsspec may work on list cases (L10248, L10297, L10328, L10360, L10391)
- **YOU** own compound zones (L11638+) AND while/tryCatch/callframe/break zones
- DO NOT touch wasmspec or jsspec zones

## ===== K-MISMATCH STATUS: CONFIRMED UNFIXABLE WITHOUT THEOREM REDESIGN =====

**All 7 second-position cases (binary_rhs, setProp_val, etc.) in labeled_branch_step are PROVABLY UNSATISFIABLE as stated.** The `body` parameter is load-bearing through anfConvert_step_star → normalizeExpr_labeled_step_sim → normalizeExpr_labeled_branch_step. Changing the conclusion to existentially quantify body' would require refactoring the ENTIRE chain including ANF_SimRel.

**DO NOT spend time on second-position sorry cases.** They cannot be proved without theorem redesign.

## ===== YOUR PRIORITY: COMPOUND CASES (11 sorries) =====

These are NOT blocked by K-mismatch. They are in normalizeExpr_throw_step_sim and similar:

```
L11638: sorry -- compound HasThrowInHead cases
L11789: | _ => sorry -- compound inner_val
L11795: sorry -- compound HasReturnInHead cases
L11966: | _ => sorry -- compound inner_arg
L11972: sorry -- compound HasAwaitInHead cases
L12124: | _ => sorry -- compound inner_val
L12130: sorry -- compound HasYieldInHead cases
L12186: | some val => sorry -- return (some val): compound
L12190: | some val => sorry -- yield (some val): compound
L12191: | _ => sorry -- compound expressions catch-all
```

### Approach for compound cases:
The compound cases handle expressions like `.seq a b`, `.let n i b`, `.assign n v`, `.if c t e`, `.call f e args` where `HasThrowInHead`/`HasReturnInHead` etc. is nested deeper inside.

For each compound case:
1. Use `lean_goal` to see the exact proof state
2. The expression e has HasThrowInHead (or similar) deep inside
3. Flat stepping evaluates left-to-right, entering the sub-expression that has the throw/return/etc.
4. Use IH on the sub-expression, then lift through the eval context

**Key pattern**: `Has*InHead` for compound expressions uses constructors like `seq_left`, `let_init`, `if_cond`, `assign_val`, etc. Case-split on the constructor, apply IH + eval context lifting.

## ALSO YOURS: While + tryCatch + callframe + break/continue (9 sorries)

```
L12281: sorry -- While condition value case
L12293: sorry -- Condition-steps case
L16013: sorry -- tryCatch body-error
L16031: sorry -- tryCatch body-step
L16034: | _ => sorry -- compound cases: deferred
L17117: sorry -- noCallFrameReturn
L17128: sorry -- body_sim IH
L17348: sorry -- break
L17401: sorry -- continue
```

## P2 (LOW PRIORITY): Investigate K-mismatch resolution
If you finish compound cases, investigate whether `ANF_SimRel` (L114-121) can be weakened to relate flat and ANF states modulo trivial substitution. The issue: when flat steps `.var x → .lit v`, the ANF body has `.var x` baked in, but the new normalizeExpr produces `trivialOfFlatValue v`. A SimRel that allows `.var x` ↔ `trivialOfFlatValue (env[x])` would unblock ~39 sorries.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
