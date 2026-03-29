# proof — CC OBJECTLIT AND CCSTATE THREADING

## STATUS: BUILD PASSES ✓. 56 grep sorries (17 ANF + 21 CC + 18 Wasm + 0 Lower).
## LAST RUN: arrayLit non-value case PROVED ✓. newObj confirmed BLOCKED (Core ignores callee/args).

## PRIORITY 0: CC objectLit non-value case (L3247)

This is the SAME pattern as your arrayLit proof. objectLit has `props` instead of `elems`.

**Key APIs** (Core has these already):
- `Core.firstNonValueProp : List (String × Core.Expr) → Option (List (String × Core.Expr) × (String × Core.Expr) × List (String × Core.Expr))`
- `Core.step_objectLit_step_prop` (Core/Semantics.lean ~L13634)

**Steps**:
1. `rw [hsc] at hconv hncfr hexprwf hd`
2. `simp [Flat.convertExpr] at hconv` — gives `sf.expr = .objectLit (convertPropList ...)`
3. `cases hcfnv : Core.firstNonValueProp props` — none = all values (sorry), some = stepping
4. For `some` case: copy arrayLit proof pattern exactly, substituting props for elems

The staging file `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean` has helpers like `convertPropList_firstNonValueProp_some/none`.

**Target: -1 sorry (objectLit 1→2, same as arrayLit, but non-value case proved)**

## PRIORITY 1: CC var captured case (L1981)

Line 1981 is a sorry for `var` when `lookupEnv envMap name = some idx`. After CC, the var becomes `.getEnv (.var envVar) idx`. Both Core and Flat look up `name` in env. Core gets a value from `sc.env`, Flat gets `.getEnv` which looks up in closure env.

The proof needs: EnvCorr relates Core env lookup to Flat env lookup. If `EnvCorr sc.env sf.env` and `lookupEnv envMap name = some idx`, then `sf.env` contains the same value at the right position.

## PRIORITY 2: CC if-else CCState threading (L2300, L2322)

These 3 sorries are about `convertExpr` state threading: the `st'` from converting `then_` branch differs from `st_a'` expected by the theorem. Look at the `st_a, st_a'` pair and see if `CCStateAgree` can be weakened or if the state threading just needs careful bookkeeping.

## DO NOT ATTEMPT: ANF sorries, Wasm sorries, CC value sub-cases (heap), newObj, functionDef, tryCatch, while_

## FILES: `VerifiedJS/Proofs/*.lean` (rw)
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
