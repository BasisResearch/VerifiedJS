# proof — ANF DEPTH INDUCTION + CC SORRY REDUCTION

## STATUS: 17 ANF sorries, 21 CC grep (18 actual), 1 Lower = ~36 actual project sorries.
## LAST 3 RUNS: EXIT code 1 or no output. YOU MUST PRODUCE RESULTS.

## STOP: DO NOT attempt objectLit/arrayLit integration
The staging proofs INCREASE sorries (1→3 per case, net +4). Skip until noCallFrameReturn and CCState lemmas exist.

## STOP: DO NOT attempt ANF hk generalization
Cascading refactor. Blocked.

## PRIORITY 0: Close ANF depth induction IH cases (-3 to -7 sorries)

You already restructured `normalizeExpr_labeled_step_sim` with `induction d` at L1598+. The 7 sorry cases at L1617, L1621, L1632, L1683, L1687, L1698, L1715 now have `ih` in scope.

**The blocker**: the continuation `k` passed to `normalizeExpr` on the sub-expression is NOT trivial-preserving (e.g., `fun t => pure (.return (some t))`).

**Solution for return-some (L1617)**:
The continuation IS trivial-preserving! `fun t => pure (.return (some t))` satisfies `∀ arg n', ∃ m', (k arg).run n' = ok (.return (some arg), m')` trivially — just unfold pure. So:
```lean
| some val =>
  -- The continuation fun t => pure (.return (some t)) IS trivial-preserving
  have hk_ret : ∀ (arg : ANF.Trivial) (n' : Nat), ∃ m',
    ((fun t => pure (ANF.Expr.return (some t))) arg).run n' = Except.ok (ANF.Expr.return (some arg), m') := by
    intro arg n'; exact ⟨n', rfl⟩
  exact ih ⟨...normalizeExpr val (fun t => pure (.return (some t))) ...⟩ hk_ret ...
```

Apply the same pattern for **yield-some (L1621, L1687)**: `fun t => pure (.yield (some t) delegate)` is also trivially trivial-preserving.

For **compound cases (L1632, L1698, L1715)**: These use `bindComplex` which generates `let tmp_N = ...` continuations. Check if `bindComplex`-generated continuations are trivial-preserving. jsspec proved `bindComplex_k_not_labeled` but we need `bindComplex_k_trivial_preserving`. If they ARE: apply ih. If NOT: these need the hk generalization (skip).

**Concrete steps**:
1. Read L1610-1720 to see exact goal structure
2. For L1617: write `hk_ret` as above, then `exact ih ...`
3. For L1621: same with yield continuation
4. For L1683, L1687: same patterns (these are the yield.labeled branch)
5. Build after each change: `lake env lean VerifiedJS/Proofs/ANFConvertCorrect.lean`
6. For L1632/1698/1715: check if bindComplex continuations are trivial-preserving

## PRIORITY 1: ANF break/continue semantic mismatch (L1851, L1853)

ANF break → `.silent`, Flat break → `.error "break:..."`. Observable traces differ.

**Investigation needed**: Does the proof need to account for labeled/while_ consuming these events? If break only appears inside while_ (which wraps with labeled), the `anfConvert_step_star` theorem may never be called directly on a break expression — it's always consumed by the labeled case first.

Check: does the labeled case at L1828 handle the break sub-step? If the labeled case produces a `.silent` event that matches the ANF break's `.silent`, the mismatch doesn't matter because break is always enclosed.

If break CAN appear at top level: this is a genuine semantics BUG. Flag it in PROOF_BLOCKERS.md but don't try to fix it.

## PRIORITY 2: CC newObj (L2680) — single sorry, possibly simple

Read convertExpr for `.newObj` and the stepping equation. If it follows the same pattern as call (arg stepping), it may be closeable with the same technique as throw-non-value.

## FILES YOU OWN
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)

## IMPORTANT
- forIn/forOf (L1132-1133): SKIP (stubs, not in supported)
- 5 value sub-cases (L2686, L2744, L2814, L2883, L2967): SKIP (need heap reasoning)
- while_ (L3232), if CCState (L2166, L2188): SKIP (CCState threading)
- objectLit/arrayLit (L3109-3110): SKIP (staging increases sorries)
- tryCatch (L3201): SKIP (complex)

## WORKFLOW
1. Attempt return-some IH application (L1617) — this is the most likely to close
2. Attempt yield-some IH applications (L1621, L1683, L1687)
3. Build and verify
4. Log to agents/proof/log.md with EXACT sorry counts before/after
