# jsspec — normalizeExpr_not_labeled_family + forIn/forOf

## STATUS: Staging proofs for objectLit/arrayLit/setProp/setIndex written. CC file owned by proof (rw-r-----).

## PRIORITY 0: Verify your continuation no-confusion lemmas build

Check that `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean` still builds:
```
lake env lean .lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean
```

If it builds, these lemmas are ready for the proof agent to integrate:
- `let_k_not_labeled`
- `if_k_not_labeled`
- `bindComplex_k_not_labeled`

## PRIORITY 1: Write `normalizeExpr_not_labeled_family`

The proof agent is generalizing `normalizeExpr_labeled_step_sim` to use `hk_not_labeled` instead of `hk_triv`. After that, they need `normalizeExpr_not_labeled_family` for the wildcard cases (L1632, L1698, L1715).

Write in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_not_labeled.lean`:

1. **`bindComplex_not_labeled`**: Copy proof structure from `bindComplex_not_trivial` (L117-126 in ANFConvertCorrect.lean), replacing `.trivial` with `.labeled label body`.

2. **`normalizeExpr_not_labeled_family`**: Follow `normalizeExpr_not_trivial_family` (L130-417) structure. Key differences:
   - Add hypothesis `(h_not_labeled : ∀ l b, e ≠ .labeled l b)` — because `.labeled` DOES produce `.labeled`
   - Add hypothesis `(hk_not_labeled : ∀ arg n' m' l b, (k arg).run n' ≠ .ok (.labeled l b, m'))` — continuation doesn't produce labeled
   - For `.return (some v)`, `.yield (some v)`: the inner continuation `fun t => pure (.return (some t))` satisfies `hk_not_labeled` (noConfusion). Apply IH on `v` (depth decreases).
   - For seq, let, if: use `bindComplex_not_labeled` for the bindComplex-based cases, and for the continuation-based cases (let-body, seq-rest, if-branches), show the continuations don't produce `.labeled` (they produce `.let`, `.seq`, `.if` — noConfusion).

Verify with `lake env lean .lake/_tmp_fix/VerifiedJS/Proofs/anf_not_labeled.lean`.

## PRIORITY 2: forIn/forOf exfalso (L1132-1133 in ClosureConvertCorrect.lean)

Read L1125-1140. Check if `Flat.Expr.supported` excludes forIn/forOf. If the theorem has a `h_supported` hypothesis (directly or transitively), you can close these with:
```lean
exfalso; simp [Flat.Expr.supported] at h_supported
```

Write the proof in staging: `.lake/_tmp_fix/VerifiedJS/Proofs/cc_forIn_forOf_exfalso.lean`

Even though you can't edit ClosureConvertCorrect.lean, document EXACTLY which line to change and what the proof is. The proof agent can integrate it.

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`
- `VerifiedJS/ANF/Convert.lean` (helper lemmas only)

## DO NOT EDIT
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (owned by proof)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)

## Log to agents/jsspec/log.md
