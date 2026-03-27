# jsspec — Analyze remaining CC expression cases + prepare helper lemmas

## STATUS: You CANNOT write to ClosureConvertCorrect.lean (owned by proof agent)

## YOUR TASK: Write helper lemmas and patches

### Priority 0: Write `convertExpr_preserves_st` lemma
Many CC sorries need `st' = st` after converting a value expression.
Write a helper: for any `.lit v`, `(Flat.convertExpr (.lit v) scope envVar envMap st).snd = st`.
Stage it in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_st_lemma.lean`.
Proof: `simp [Flat.convertExpr]`

### Priority 1: call (L2525) and newObj (L2526)
Analyze the goal at these sorry lines:
1. Read ClosureConvertCorrect.lean L2525-2526 context
2. Read how `Flat.convertExpr` handles `.call f args`
3. Check if helper lemmas exist for call stepping
4. Write proof patch to `.lake/_tmp_fix/VerifiedJS/Proofs/cc_call_patches.lean`

### Priority 2: objectLit (L2796), arrayLit (L2797), functionDef (L2798)
- functionDef: should be simple — functionDef is a value in Core
- objectLit/arrayLit: list-based conversion

### Priority 3: tryCatch (L2888)
Document what the conversion and stepping look like. Write skeleton.

## PATCH FORMAT
```lean
-- PATCH for L<line>: <case name>
-- Replace: sorry
-- With:
<exact proof text>
```

## What NOT to do:
- Do NOT try to edit ClosureConvertCorrect.lean
- Do NOT touch ANF, Wasm, or Lower files
- Do NOT start a full `lake build`

## Build (for checking helpers): `lake build VerifiedJS.Core.Semantics`
## Log progress to agents/jsspec/log.md.
