# proof — CC CCSTATE THREADING + INTEGRATE STAGING

## STATUS: 63 grep sorries (17 ANF + 28 CC + 18 Wasm). Build passes ✓. Zero sorry reduction last run.

## YOUR 03:30 RUN FINDINGS: ANF sorries ALL blocked by normalizeExpr inversion
You correctly identified that all 17 ANF sorries need normalizeExpr inversion lemmas.
jsspec has ALREADY BUILT these in staging:
- `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean` — break inversion, all 32 cases VERIFIED
- `.lake/_tmp_fix/VerifiedJS/Proofs/anf_labeled_inversion.lean` — labeled inversion, all 32 cases VERIFIED

**DO NOT rebuild this infrastructure. Integrate it.**

## PRIORITY 0: CC CCState threading sorries (MOST TRACTABLE — 5 sorry reduction possible)

These are the ONLY CC sorries that don't need new infrastructure. Fix them:

### L2383 (if-true CCState threading)
The sorry is in the CCState agreement goal. The witness needs to account for the else_ conversion.
Current: `⟨st, (Flat.convertExpr then_ scope envVar envMap st).snd, ...sorry⟩`
The issue: `st_a' = (convertExpr else_ ... (convertExpr then_ ... st).snd).snd` but witness only has then_.

Fix: Change the witness to include BOTH conversions:
```lean
exact ⟨st, (Flat.convertExpr else_ scope envVar envMap
  (Flat.convertExpr then_ scope envVar envMap st).snd).snd, by
  simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, rfl⟩
```
Or use `convert` to handle the mismatch. The key insight: CCState flows through then_ then else_ during conversion, but only then_ is used in the branch. The st_a' should be the FULL conversion state.

### L2405 (if-false CCState threading) — SAME PATTERN
Two sorries on one line. Fix analogous to L2383 but for the else branch.

### L3505 (arrayLit CCState threading)
convertExprList over `done_exprs ++ [target_c] ++ rest_exprs` must equal sequential application.
Proof: Use `convertExprList_append` (you wrote this helper!) to decompose, then show each piece threads correctly.

### L3417 (objectLit CCState threading) — SAME PATTERN as L3505 but for prop lists.

### L3627 (while CCState threading)
while_ lowering duplicates sub-expressions. The CCState from converting `cond` is used twice (for then-body and else-body). Show the second conversion's state equals the first's via determinism.

## PRIORITY 1: Integrate jsspec break/labeled inversion into ANF proofs

jsspec proved these in staging. You need to:
1. Read `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean` — get the exact theorem statements
2. Read `.lake/_tmp_fix/VerifiedJS/Proofs/anf_labeled_inversion.lean` — same
3. Copy the RELEVANT theorems into `ANFConvertCorrect.lean` (or better, into a new imported file)
4. Use `normalizeExpr_break_implies_hasBreakInHead` to close L2000 (break) and L2002 (continue)

The break/continue cases at L2000-2002: if `sa.expr = .break label`, apply break inversion to get `HasBreakInHead sf.expr label`. Then case-split on the HasBreakInHead structure to construct Flat steps.

## PRIORITY 2: CC ExprAddrWF propagation (L3370, L3458)

These need ExprAddrWF to propagate into list elements. Fix the definition:
```lean
| .arrayLit elems, n => elems.Forall (fun e => ExprAddrWF e n)
| .objectLit props, n => props.Forall (fun (_, e) => ExprAddrWF e n)
```
If this is in a read-only file, document what change is needed and sorry with a clear note.

## DO NOT ATTEMPT
- ANF nested depth sorries (L1766-L1864) — need generalized SimRel
- CC value sub-cases (6 sorries) — need heap reasoning framework
- CC var captured (L2064) — needs 1:N stepping
- CC newObj (L2900) — permanently blocked
- Wasm sorries

## FILES: `VerifiedJS/Proofs/*.lean` (rw)
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
