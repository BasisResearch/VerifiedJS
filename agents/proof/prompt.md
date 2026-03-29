# proof — INLINE ANFInversion + CC CCSTATE THREADING

## STATUS: 61 sorries (17 ANF + 26 CC + 18 Wasm + 0 Lower). CC went 27→26. Good.

## CRITICAL INFRASTRUCTURE: ANFInversion content must be INLINED

**Nobody can create new files** — all directories are root:pipeline 750. The staging file
`.lake/_tmp_fix/VerifiedJS/Proofs/ANFInversion.lean` (1425 lines, 0 sorry) CANNOT be
copied to a new file. The only option is to APPEND its content into `ANFConvertCorrect.lean`.

### How to inline:
1. Read `.lake/_tmp_fix/VerifiedJS/Proofs/ANFInversion.lean` (skip the top comment + imports — they're already in ANFConvertCorrect)
2. Find a good insertion point in `ANFConvertCorrect.lean` — just BEFORE the first sorry (around L1760)
3. Paste the theorem bodies (starting from `theorem ANF.bindComplex_never_break_general` through end)
4. The namespace is `VerifiedJS` in ANFInversion but `VerifiedJS.Proofs` in ANFConvertCorrect — you may need to adjust: open the namespace or prefix references
5. `lake build VerifiedJS.Proofs.ANFConvertCorrect` — must still pass
6. If it fails, sorry-back any broken theorems and keep the ones that work

This is P0. Without these inversion lemmas, the break/continue ANF sorries (L2000-2002) cannot be closed.

## PRIORITY 1: CC CCState threading at L2383, L2405

You're already working on these. Key insight for L2383:

The sorry at L2383 is the last component of an existential witness for the CC_SimRel.
The goal is likely `CCStateAgree st_a' st_a''` or a Prod.mk equality.

Use `lean_goal` at L2383 to check the EXACT goal type before attempting anything.

For L2405: two sorries. One is likely a `Prod.mk.eta` / `Prod.ext` equality, the other
is likely `CCStateAgree`. Use `lean_goal` at each position.

## PRIORITY 2: CC value sub-cases (L2899, L3089, L3159, L3228, L3313)

These 5 sorries all say "value sub-case (heap reasoning needed)". They follow a pattern:
- callee/arg is already a value (`some cv`)
- Need to show the Flat step matches the Core step when operating on a converted value
- Blocked by heap injection reasoning

If heap injection is already set up in the SimRel, these may be closeable with
`convertValue_inj` or `HeapInj.get_corr`. Check with `lean_hover_info` on `HeapInj`.

## PRIORITY 3: CC forIn/forOf (L1148-1149)

These theorems are FALSE as stated. `forIn`/`forOf` convert to `.lit .undefined` which
HAS a value (`Flat.exprValue? (.lit .undefined) = some .undefined`). But the theorem
claims `Flat.exprValue? (convertExpr e ...) = none` for ALL non-value Core expressions.

Fix: Add a hypothesis `e.supported = true` that excludes forIn/forOf. Or: add
`| forIn => rfl` / `| forOf => rfl` if the `Core.exprValue?` actually gives `some` for
these (check!). The real fix is to exclude unsupported constructors.

## WORKFLOW
1. `lean_goal` at each sorry BEFORE attempting anything
2. `lean_multi_attempt` to test candidate tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build fails, sorry it back IMMEDIATELY

## FILES
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw — INLINE ANFInversion here)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw — CC sorries)
- `.lake/_tmp_fix/VerifiedJS/Proofs/ANFInversion.lean` (read only — source material)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
