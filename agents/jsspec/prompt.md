# jsspec — BREAK INVERSION + OBJECTLIT STAGING

## STATUS: Your infrastructure work is excellent. 55 total sorries, ZERO change in 4 hours. We need your work to CONVERT to sorry reductions.

## PRIORITY 0: normalizeExpr break SOURCE CHARACTERIZATION (continued)

This is the KEY MISSING PIECE for -2 ANF sorries. You were redirected to this at 18:05. Continue your break inversion work in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`.

Reminder of what's needed:

Given `normalizeExpr e k = .ok (.break label, m)` with `k` trivial-preserving, prove that Flat can step from `{expr := e}` to `{expr := .break label}` in zero or more steps.

Key cases:
1. `e = .break l` directly → zero steps
2. `e = .seq a b` where `exprValue? a ≠ none` → one step (drop value), then recurse on b
3. `e = .seq a b` where a normalizes to value via bindComplex → multi-step a, then recurse on b

The proof agent CANNOT close ANF L1948/L1950 without this lemma. Even a partial version (just cases 1+2) is valuable.

## PRIORITY 1: objectLit/arrayLit CC helpers

The proof agent is about to work on CC objectLit (L3129). Check if more staging helpers are needed beyond what you already have in `cc_objectLit_arrayLit_helpers.lean`.

Specifically, the proof agent needs:
1. `Flat.step?_objectLit_prop_step`: When first prop is non-value, Flat steps the inner expression
2. `Core.step?_objectLit_prop_step`: Same for Core
3. `convertPropList_cons`: How convertExpr relates to stepping through prop list

Check if these exist. If not, stage them in `.lake/_tmp_fix/`.

## PRIORITY 2: Complete "leaf not-break" lemmas

For the master break inversion, you need: `normalizeExpr (.X ...) k` with trivial-preserving k NEVER produces `.break` for each non-break, non-seq, non-let constructor. Complete the set for:
- `.getProp`, `.setProp`, `.binary`, `.unary`, `.typeof`, `.deleteProp`
- `.assign`, `.if`, `.while_`, `.call`, `.newObj`

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`

## DO NOT EDIT
- `VerifiedJS/Proofs/*.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)
- `VerifiedJS/ANF/Semantics.lean` (owned by wasmspec)

## LOG to agents/jsspec/log.md
