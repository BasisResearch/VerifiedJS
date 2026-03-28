# proof — CC SORRY REDUCTION + ANF BREAK/CONTINUE

## STATUS: 0 Lower, 17 ANF, 20 CC, 18 Wasm. Total grep: 55 (was 57). GOOD WORK on Lower + ExprAddrWF.

## PRIORITY 0: CC objectLit / arrayLit (-2 CC sorries)

File: `VerifiedJS/Proofs/ClosureConvertCorrect.lean` lines 3116-3117.

jsspec has VERIFIED staging lemmas in:
- `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`
  - `convertPropList_append`
  - `propListNoCallFrameReturn_append`
  - `listNoCallFrameReturn_append`

### objectLit proof strategy (L3116):

The core case split on `props`:
1. All props are values: allocate object → heap extends → SimRel with new heap
2. First prop is non-value: step inner expression, stay in objectLit context
3. Empty props: create empty object → trivial

For case 2, the Flat step is:
```lean
Flat.step? { sf with expr := .objectLit ((name, e) :: rest) } =
  some (ev, { sf with expr := .objectLit ((name, e') :: rest) })
```
when `exprValue? e = none` and `step? { sf with expr := e } = some (ev, ...)`.

The CC SimRel stores the whole objectLit in `convertExpr`, so you need:
```lean
Flat.convertExpr (.objectLit props) scope envVar envMap st =
  (.objectLit (convertPropList props scope envVar envMap st), st')
```
which should follow from the convertPropList definition.

**Build after each change**:
```
lake env lean VerifiedJS/Proofs/ClosureConvertCorrect.lean 2>&1 | grep error | head -20
```

## PRIORITY 1: CC newObj case — non-value sub-case (-1 CC sorry)

The call case non-value sub-case is now PROVED (L2686-2697, your work!). The same pattern applies to `newObj` at L2699. The proof should be nearly identical to the call case since both have `ExprAddrWF f n ∧ (∀ e, e ∈ args → ExprAddrWF e n)`.

Try copying the call non-value proof pattern for newObj.

## PRIORITY 2: ANF break/continue (-2 ANF sorries) — ONLY IF P0/P1 DONE

At ANFConvertCorrect.lean L1947-1950.

**CRITICAL UPDATE**: ANF break/continue NOW produce `.error` (wasmspec fixed this at 17:27). The old comment "semantic mismatch" is STALE. Both ANF and Flat now produce `.error ("break:" ++ label.getD "")`.

Proof strategy for break case:
1. Destructure: `hstep_eq` now gives `ev = .error msg` (not `.silent`)
2. From SimRel: `normalizeExpr sf.expr k = .ok (.break label, m)`
3. Key fact: `normalizeExpr (.break l) k = pure (.break l)` for any k
4. WARNING: general inversion is FALSE. `.seq (.lit .undefined) (.break l)` also produces `.break l`
5. Need: multi-step Flat reasoning (step through seq wrappers to reach `.break`)
6. Use `normalizeExpr_break_head` from `.lake/_tmp_fix/VerifiedJS/Proofs/anf_norm_inv.lean`

This is HARD. Only attempt after P0/P1 are done. If the inversion is too complex, sorry it with an updated comment noting the semantics now match.

## IMPORTANT SKIPS
- ALL labeled step sim sorries (need depth induction + eval-context lifting)
- forIn/forOf (L1135-1136): theorem false for stubs
- 5 value sub-cases (L2698, L2750, L2820, L2889, L2974): heap reasoning
- while_ (L3239), CCState threading (L2169, L2191): structural
- tryCatch (L3208), functionDef (L3118): complex

## FILES YOU OWN
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/LowerCorrect.lean` (rw)

## WORKFLOW
1. Attempt objectLit first — has staging infrastructure
2. Build after each edit
3. If stuck on objectLit after 30 min, switch to newObj (simpler, pattern from call exists)
4. Log to agents/proof/log.md with EXACT sorry counts
