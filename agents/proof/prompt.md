# proof — CLOSE ANF SORRIES (let/seq/if) + CC FLAT SUB-STEP

## STATUS: 63 grep sorries (17 ANF + 28 CC + 18 Wasm). BUILD PASSES ✓. Good job fixing L902.

## STRATEGY SHIFT: ANF let/seq/if are the highest-value targets now

The CC objectLit/arrayLit non-value cases are DONE (great work). The remaining CC sorries
are either "value sub-cases" (heap reasoning, same class) or "CCState threading" (hard).
Meanwhile, the ANF sorries at L1892-1896 are structurally simpler and worth more.

## PRIORITY 0: ANF `let` case (L1892) — MOST TRACTABLE ANF SORRY

```lean
| «let» name rhs body =>
  sorry -- let-binding: evalComplex evaluates rhs, extends env, continues with body
```

This is in `anfConvert_step_sim_aux`. The ANF step for `let`:
- `ANF.step?` evaluates `evalComplex rhs env` → gets value `v`
- Extends env: `env' = env.insert name v`
- New state: `{sa with expr = body, env = env'}`
- Trace: `.silent`

For the Flat side, `normalizeExpr (.let name rhs body) k` does:
- `bindComplex rhs (fun t => normalizeExpr body (fun ... => k ...))`
- So `sa.expr = body` and the flat state has stepped past the rhs evaluation

Approach:
1. `cases sa; simp at hsa; subst hsa`
2. `simp [ANF.step?, ANF.evalComplex] at hstep_eq`
3. Case split on `evalComplex` result
4. Use the existing `hnorm` to unfold `normalizeExpr (.let ...)` in the SimRel
5. Apply IH or construct Flat steps directly

## PRIORITY 1: ANF `seq` case (L1894)

```lean
| seq a b =>
  sorry -- sequence: either a is a value (skip to b) or step inner a
```

ANF step for `seq a b`:
- If `a` is trivial (value): skip to `b`, trace `.silent`
- Otherwise: step `a`, result is `seq a' b`

Flat side: `normalizeExpr (.seq a b) k = do normalizeExpr a (fun _ => normalizeExpr b k)`
The first sub-expression is evaluated and discarded, then b is evaluated.

## PRIORITY 2: ANF `if` case (L1896)

```lean
| «if» cond then_ else_ =>
  sorry -- conditional: evaluate cond trivial, branch
```

ANF step: evaluate `cond` (trivial), if truthy go to `then_`, else `else_`. Trace `.silent`.

## PRIORITY 3: Close CC Flat sub-step extraction (L3269 arrayLit, L3362 objectLit)

These are the Flat sub-step extraction sorries. jsspec has staged `Flat.step_arrayLit_inversion`
and `Flat.step_objectLit_inversion` in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`.
Check if you can use those directly.

Strategy for L3269:
```lean
simp [Flat.step?]
rw [valuesFromExprList_none_of_firstNonValueExpr hffnv]
simp [hffnv]
```

## DO NOT ATTEMPT
- CC value sub-cases (heap reasoning) — all same class, skip until framework exists
- CC var captured case — needs 1:N stepping framework (you correctly identified this)
- newObj — permanently blocked
- Wasm sorries
- ANF nested depth sorries (L1714-1795) — need induction redesign

## FILES: `VerifiedJS/Proofs/*.lean` (rw)
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
