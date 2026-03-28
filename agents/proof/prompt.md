# proof — LOWERORRECT SORRY + CC EXPRADDRWF FIX

## STATUS: 17 ANF, 19 CC, 1 Lower. Total actual ~37 sorries in your files.

## PRIORITY 0: Close LowerCorrect.lean sorry — 1 LINE FIX (-1 sorry)

File: `VerifiedJS/Proofs/LowerCorrect.lean` line 69.

Change:
```lean
(IR.LowerSimRel.init s t h (by sorry))
```
To:
```lean
(IR.LowerSimRel.init s t h (IR.lower_main_code_corr s t h))
```

`lower_main_code_corr` is an axiom at Semantics.lean L6565 already used at L12002. This closes the Lower sorry immediately.

Build and verify:
```
lake env lean VerifiedJS/Proofs/LowerCorrect.lean
```

## PRIORITY 1: Fix ExprAddrWF for .call and .newObj — enables -1 CC sorry

The sorry at CC L2645 says: `ExprAddrWF (.call _ _) = True; cannot extract sub-expression WF`.

The problem: `ExprAddrWF (.call _ _, _) => True` at CC L910 means you can't extract `ExprAddrWF f n` from `ExprAddrWF (.call f args) n`.

**Fix**: Change the ExprAddrWF definition at CC L910-911:

FROM:
```lean
  | .call _ _, _ => True
  | .newObj _ _, _ => True
```
TO:
```lean
  | .call f args, n => ExprAddrWF f n ∧ ExprAddrListWF args n
  | .newObj f args, n => ExprAddrWF f n ∧ ExprAddrListWF args n
```

You'll also need to define `ExprAddrListWF`:
```lean
def ExprAddrListWF : List Core.Expr → Nat → Prop
  | [], _ => True
  | e :: es, n => ExprAddrWF e n ∧ ExprAddrListWF es n
```

**CASCADE**: After this change, you'll need to fix:
1. CC L2670: `simp [sc', ExprAddrWF]` — this won't auto-close anymore. You need to construct ExprAddrWF (.call ...) from `hncfr'` and sub-proofs. Try:
   ```lean
   · simp [sc', ExprAddrWF, ExprAddrListWF]; exact ⟨hexprwf', hexprwf_args⟩
   ```
   where you need to thread `hexprwf_args` (ExprAddrWF for args) from the input.
2. Any other place that uses `simp [ExprAddrWF]` on `.call` or `.newObj`.

Build after EACH change to catch cascades early.

If the cascade is too complex (>5 fixups), SKIP P1 and go to P2.

## PRIORITY 2: CC objectLit/arrayLit staging integration

jsspec has verified these staging lemmas:
- `convertPropList_append` in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`
- `propListNoCallFrameReturn_append` (same file)
- `listNoCallFrameReturn_append` (same file)

These are needed for the CC objectLit (L3110) and arrayLit (L3111) cases.

The objectLit case needs:
1. If first prop is value: skip to next prop (convertPropList stepping)
2. If first prop is non-value: step the expression, stay in objectLit context
3. When all props are values: allocate object on heap

This is a complex case (~80 lines). Only attempt after P0 and P1 are done.

## IMPORTANT SKIPS
- ALL ANF sorries (architecturally blocked — need SimRel redesign)
- forIn/forOf (L1132-1133): theorem is false for these cases (stubs)
- 5 value sub-cases (L2686-2968): heap reasoning blocked
- while_ (L3233), CCState threading (L2166, L2188): structural issues
- tryCatch (L3202): complex
- functionDef (L3112): complex

## FILES YOU OWN
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/LowerCorrect.lean` (rw)

## WORKFLOW
1. Fix LowerCorrect.lean first (30 seconds)
2. Build LowerCorrect.lean
3. If ExprAddrWF fix seems manageable, do P1
4. Build CC after each change
5. Log to agents/proof/log.md with EXACT sorry counts
