# proof — COMPOUND THROW: SECOND-OPERAND + LIST CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T08:05
- ANF: **30** real sorries. CC: 12. Total: **42**.
- 12 trivial-mismatch sorries (L11366-L11737): BLOCKED, DO NOT TOUCH.
- L18325 (HasNonCallFrameTryCatch): wasmspec owns it. DO NOT TOUCH.
- You added 16 first-operand cases at 08:01. GREAT. Now close the catch-all.

## P0: L15944 `| _ => sorry` — CLOSE THIS NOW

You proved 16 first-operand cases using `throwInHead_compound_lift`. The remaining `| _ =>` catches:

**Second-operand cases** (the first sub-expression is already a value):
- `binary_rhs`: `binary op (.lit lv) rhs` — throw is in rhs
- `setProp_value`: `setProp (.lit obj) prop val` — throw is in val
- `getIndex_idx`: `getIndex (.lit obj) idx` — throw is in idx
- `setIndex_idx`: `setIndex (.lit obj) idx val` — throw is in idx
- `setIndex_value`: `setIndex (.lit obj) (.lit iv) val` — throw is in val
- `call_env`: `call (.lit f) env args` — throw is in env
- `newObj_env`: `newObj (.lit f) env args` — throw is in env

For these, you need a SECOND-OPERAND variant of throwInHead_compound_lift:
```lean
private theorem throwInHead_compound_lift_second
    {outer : Flat.Expr} {inner : Flat.Expr}
    (h_sub : HasThrowInHead inner)
    (h_val : Flat.exprValue? outer.firstChild = some _)  -- first operand is value
    (h_ctx : ∀ s inner' hv t si, step? ⟨inner, ...⟩ = some (t, si) → ...)
    (h_err : ...)
    (ih : ...) : ... := ...
```

OR just inline: since the first operand is a `.lit`, `step?` on the compound expression directly steps the second operand. The ctx/error lemmas for second-operand position should exist (step?_binary_rhs_ctx etc.).

**List cases** (throw is in first non-value element):
- `call_args`: `call (.lit f) (.lit e) args` — throw is in args list
- `newObj_args`: `newObj (.lit f) (.lit e) args` — throw is in args list
- `makeEnv_elem`: `makeEnv values` — throw is in values list
- `objectLit_value`: `objectLit props` — throw is in props list
- `arrayLit_elem`: `arrayLit elems` — throw is in elems list

For list cases, use the HasThrowInHeadList/Props infrastructure you already proved in HasThrowInHead_step_nonError. The key: decompose via firstNonValue, step the first non-value element, reconstruct.

### EXECUTION:
1. Split `| _ =>` into individual match arms for EACH remaining constructor
2. Prove each second-operand case (7 cases) — these follow the same pattern as first-operand but use the _rhs/_val/_idx/_env ctx/error lemmas
3. Prove each list case (5 cases) — use firstNonValue decomposition + list IH
4. If ANY case is too hard, sorry it individually — 12 individual sorries > 1 opaque catch-all

### AFTER P0: Move to P1 (L23611-L23845)
These 5 sorries use the SAME infrastructure pattern for HasAwaitInHead/HasYieldInHead compound cases.

## FULL SORRY MAP (30 total):
- **BLOCKED (12)**: L11366-L11737 (trivial mismatch)
- **WASMSPEC (1)**: L18325
- **P0 (1)**: L15944 (compound throw catch-all) ← YOU ARE HERE
- **P1 (5)**: L23611, L23784, L23840, L23844, L23845 (await/yield/return compound)
- **P2 (2)**: L23935, L23947 (while condition)
- **P3 (2)**: L24672, L24712 (if-branch K-mismatch)
- **P4 (3)**: L25553, L25571, L25574 (tryCatch)
- **P5 (4)**: L26901, L26902, L27121, L27192 (end-of-file)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
