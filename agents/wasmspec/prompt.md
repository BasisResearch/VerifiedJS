# wasmspec — CLOSE HasReturnInHead_Steps_steppable (L13264) + COMPOUND SORRIES

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T09:00
- Total: 46 sorries (ANF 31, CC 15). DOWN from 51.
- **YOU just closed 6 callStack sorries (-5 net). GOOD WORK.**
- You introduced 1 new sorry at L13264 (HasReturnInHead_Steps_steppable). Close it.
- Remaining wasmspec-owned: L12969, L13264, L13415, L13771, L13944, L14000, L14004, L14005 = 8 sorries

## P0: HasReturnInHead_Steps_steppable (L13264) — HIGHEST PRIORITY

This is the sorry YOU introduced to close the callStack sorries. It states:

```lean
private theorem HasReturnInHead_Steps_steppable
    (h_a : HasReturnInHead a)
    (hsteps : Flat.Steps ⟨a, env, heap, trace, funcs, cs⟩ evs_pre smid)
    {t : Core.TraceEvent} {smid' : Flat.State}
    (hstep : Flat.step? smid = some (t, smid')) :
    HasReturnInHead smid.expr
```

**What this says**: If `a` has `HasReturnInHead`, and we take some steps to `smid`, and `smid` can step further (to `smid'`), then `smid.expr` still has `HasReturnInHead`.

**Proof approach**: Induction on `hsteps`:
1. **Base case** (`Steps.refl`): `smid = ⟨a, env, heap, trace, funcs, cs⟩`, so `smid.expr = a`, and `h_a` directly gives `HasReturnInHead smid.expr`.
2. **Step case** (`Steps.step`): We have `step? ⟨a, ...⟩ = some (ev, s')` and `Steps s' evs' smid`. By IH we need `HasReturnInHead s'.expr`. This requires **HasReturnInHead preservation through a single step when the result can still step**.

So the core sub-lemma needed is:
```lean
private theorem HasReturnInHead_step_preserved
    (hret : HasReturnInHead e)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf'))
    (hsteppable : ∃ t sf'', Flat.step? sf' = some (t, sf'')) :
    HasReturnInHead sf'.expr
```

**Why this works**: HasReturnInHead tracks `.return` in head position. When `e` steps:
- If `e = .return none`: steps to `.lit .undefined` (a value, can't step further → contradiction with hsteppable)
- If `e = .return (some (.lit v))`: steps to `.lit v` (value → contradiction)
- If `e = .return (some inner)` where inner steps: `sf'.expr = .return (some inner')`, still HasReturnInHead
- If `e = .seq a b` with HasReturnInHead a: if a→a' (non-value): sf'.expr = .seq a' b, need HasReturnInHead a' (by IH). If a→value: sf'.expr = b, which may NOT have HasReturnInHead. But wait — does b step? If it does, we have hsteppable for b. But b might step without HasReturnInHead (e.g., b = .seq x y).

**THE HARD CASE**: `seq_left a b` where `a` steps to a value. Then `sf'.expr = b`. Need `HasReturnInHead b` but we only know `HasReturnInHead (.seq a b)` which gives `HasReturnInHead a`. The `b` part may not have HasReturnInHead.

**SOLUTION**: Use `NoNestedAbrupt` or a similar invariant. Check if `hasReturnInHead_return_steps` (L13269) provides any constraint on `b`. Or: check whether in the ACTUAL callsite (L13358-13361), the steps are bounded by the error event, meaning `b` is never reached.

### STEP-BY-STEP
1. Run `lean_goal` at L13264 to see exact hypotheses
2. Try the base case: `cases hsteps` or `induction hsteps`
3. For the refl case: `exact h_a`
4. For the step case: need HasReturnInHead preservation
5. Check if `NoNestedAbrupt` or `hna` is available in the context
6. If the seq_left value case is blocked, try a different approach: prove the two callStack conditions DIRECTLY preserved through steps, instead of going through HasReturnInHead

## P1: L13415 (remaining compound HasReturnInHead)

After P0, expand `| _ => sorry` at L13415 into explicit constructor matches. Each should follow the seq_left pattern you already proved.

## P2: Compound cases L13771, L13944 (HasAwait/Yield)

Same architecture as HasReturnInHead. If the pattern from P0 works, adapt for HasAwaitInHead and HasYieldInHead.

## P3: L14000, L14004, L14005 (return/yield .let + compound)

Lower priority. Attempt after P0-P2.

## SKIP (BLOCKED or proof-owned)
- L10183-L10554 (trivialChain — proof agent)
- L14095-14872 (while/if — BLOCKED)
- L15713-15734 (tryCatch — BLOCKED)
- L17061-17362 (BLOCKED)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasReturnInHead_Steps_steppable L13264" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
