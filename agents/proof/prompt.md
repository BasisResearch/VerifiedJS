# proof — ANF SEMANTIC FIX FOLLOWUP + LET/SEQ/IF CASES

## STATUS: 17 ANF sorries, 19 CC sorries. wasmspec is fixing ANF semantics for break/continue/return/throw.

## BLOCKED UNTIL wasmspec COMPLETES:
- break (L1851), continue (L1853): WAIT for ANF semantics fix (`.silent` → `.error`)
- return (L1823): WAIT for ANF semantics fix
- throw (L1819): WAIT for ANF semantics fix (`.error "throw"` → `.error (valueToString v)`)

Once wasmspec changes ANF/Semantics.lean, these 4 sorry cases become provable because ANF and Flat will produce matching `.error` events. The proof pattern for each:
```lean
| «break» label =>
  obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
  simp only [] at hsa; subst hsa
  simp [ANF.step?, ANF.pushTrace] at hstep_eq
  obtain ⟨rfl, rfl⟩ := hstep_eq
  -- Now ev = .error ("break:" ++ label.getD ""), sa' has .trivial .litUndefined
  -- sf.expr normalizes to .break label, so sf.expr = .break label (by normalizeExpr_break)
  -- Flat.step? on .break label produces the SAME .error event
  -- Use normalizeExpr inversion to determine sf.expr
  sorry -- fill in after semantics fix
```

## PRIORITY 0: Close let/seq/if cases (L1795-1799) — 3 sorries

These DO NOT have semantic mismatches. They need normalizeExpr inversion + Flat evaluation context lifting.

### let (L1795)
When `sa.expr = .let name rhs body`:
1. `normalizeExpr sf.expr k` produced `.let name rhs body`
2. `sf.expr` could be `.let fname frhs fbody` where normalizeExpr unwraps it
3. ANF step?: evaluates rhs (complex expr), extends env, continues with body
4. Need: Flat steps showing sf takes matching steps

**Approach**: Use `cases sf.expr` (from SimRel, we know normalizeExpr sf.expr k = .let ...). For each Flat constructor, check if normalizeExpr can produce .let. Most can't (exfalso). For `.let fname frhs fbody`, normalizeExpr first normalizes frhs, then in continuation normalizes fbody. Show Flat steps inner frhs or, if frhs is value, steps to fbody.

### seq (L1797)
Similar pattern to let but simpler. `normalizeExpr (.seq a b) k = normalizeExpr a (fun _ => normalizeExpr b k)`.

### if (L1799)
`normalizeExpr (.if c t e) k` normalizes c first. If c is a value, produces `.if cTriv then_anf else_anf`. The ANF step evaluates cTriv and branches.

**For all three**: The HARDEST part is the normalizeExpr inversion lemma. You need:
```lean
-- If normalizeExpr sf.expr k = .let name rhs body, characterize sf.expr
-- Option 1: sf.expr = .let fname frhs fbody (direct)
-- Option 2: sf.expr = .seq a b where a normalizes and continuation produces .let
-- etc.
```

This is a full induction on `sf.expr` and is ~100+ lines. Consider writing it as a separate lemma `normalizeExpr_let_inversion`.

**Simpler alternative**: Instead of full inversion, use the fact that `ExprWellFormed sf.expr sf.env` constrains sf.expr. If ExprWellFormed excludes certain forms, fewer cases needed.

## PRIORITY 1: yield/await unsupported — close with program-level argument

yield (L1825) and await (L1827): These are unsupported (`Core.Expr.supported` returns false for yield/await). If the Flat expression is supported, normalizeExpr can't produce yield/await.

You need a lemma: `sf.expr.supported = true → (normalizeExpr sf.expr k).run n = ok (e, m) → e ≠ .yield _ _ ∧ e ≠ .await _`

This requires induction on sf.expr but each case is straightforward. If you prove this, yield/await become exfalso.

**But**: anfConvert_step_star doesn't have a supported hypothesis. You'd need to add `h_supported : sf.expr.supported = true` to the theorem signature AND thread it from compiler_correct.

## PRIORITY 2: CC newObj (L2680) — single sorry

## FILES YOU OWN
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)

## IMPORTANT SKIPS
- depth induction IH cases (L1617-1715): SKIP, continuation not trivial-preserving, needs hk generalization
- forIn/forOf (L1132-1133): SKIP (stubs)
- 5 value sub-cases (L2686-2968): SKIP (heap reasoning)
- while_ (L3232), CCState threading (L2166, L2188): SKIP
- objectLit/arrayLit (L3109-3110): SKIP (staging increases sorries)
- tryCatch (L3201 CC, L1821 ANF): SKIP (complex)

## WORKFLOW
1. Check if wasmspec has updated ANF/Semantics.lean yet
2. If yes: close break/continue/return/throw (L1819, 1823, 1851, 1853)
3. If no: work on let/seq/if normalizeExpr inversion
4. Build after each change
5. Log to agents/proof/log.md with EXACT sorry counts
