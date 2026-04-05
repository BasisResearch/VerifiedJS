# wasmspec — CLOSE hpres sorries (16 of them!) then exotic/seq_right/trivialChain

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.6GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11200-11650 (tryCatch) and L12700-13015 (break/continue/return)
- **YOU** own L1795-1895 (Steps_ctx_lift infrastructure) AND L8000-10933 (normalizeExpr step sim)
- DO NOT touch lines outside your range

## YOUR ZONE: ~28 sorries. GROUP E IS DONE — GREAT WORK!

## PRIORITY 1: hpres (16 sorries — L10577, 10601, 10623, 10647, 10667, 10686, 10705, 10724 + 8 symmetric in false branch)

ALL hpres sorries have the SAME pattern. The goal at each is:
```lean
∀ smid evs1, Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs1 smid →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1
```

### THE APPROACH — Add `Steps_ctx_lift_pres` helper (~L1895):

The key insight: `Steps_ctx_lift` produces wrapped steps from inner steps. The inner steps preserve funcs/cs/trace (via `hpres_c`/`hpres_a` from IH). The wrapping context (`.if · then else`, `.seq · b`, etc.) only changes `.expr`, not funcs/cs. Therefore the wrapped steps ALSO preserve funcs/cs/trace.

**Step 1**: Add a general preservation lemma right after `Steps_await_ctx` (after L1884):
```lean
/-- Steps through a eval context preserve funcs/callStack when inner steps preserve them. -/
private theorem Steps_pres_from_inner
    {e : Flat.Expr} {env : Flat.Env} {heap : Core.Heap} {trace : List Core.TraceEvent}
    {funcs : Array Flat.FuncDef} {cs : List Flat.Env} {evs : List Core.TraceEvent}
    {sf' : Flat.State}
    (hsteps : Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs sf')
    (hall_silent : ∀ ev ∈ evs, ev = .silent) :
    ∀ smid evs1, Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs1 smid →
      smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1 := by
  intro smid evs1 hmid
  induction hmid with
  | refl _ => simp
  | tail hstep ih_steps =>
    -- Single step preserves funcs/cs when step is silent
    -- Use that Flat.step? for non-error, non-call-frame steps preserves funcs/cs
    sorry
```

Actually, this is hard to prove generally. SIMPLER APPROACH — prove it by case:

**Step 1 (SIMPLE)**: At each hpres sorry, the wrapped steps `hwsteps` come from `Steps_*_ctx` which uses `Steps_ctx_lift`. The input `hpres_c` (or `hpres_a`, etc.) says inner steps preserve funcs/cs. Each wrapping step?_*_ctx preserves funcs/cs because it only changes expr. So:

```lean
· -- hpres
  intro smid evs1 hsteps_mid
  -- The steps from ⟨e, env, heap, trace, funcs, cs⟩ go through the eval context.
  -- Each single step either wraps an inner step (preserves funcs/cs) or is the refl step.
  -- Since all events are silent and inner steps preserve funcs/cs, so do outer steps.
  exact Steps_ctx_lift_preserves _ hsteps_mid
```

Actually, the simplest approach: USE `hpres_c` (the IH-provided preservation) directly.

**Check** `lean_goal` at L10577 to see what exactly is needed. Then try:
```lean
lean_multi_attempt at L10577 column 8
["intro smid evs1 h; exact Steps_if_cond_pres then_flat else_flat hpres_c h",
 "intro smid evs1 h; induction h with | refl _ => simp | tail hs ih => sorry",
 "exact fun smid evs1 h => ⟨(Steps_if_cond_ctx_pres hpres_c h).1, (Steps_if_cond_ctx_pres hpres_c h).2.1, (Steps_if_cond_ctx_pres hpres_c h).2.2⟩"]
```

### CONCRETE APPROACH for hpres:

1. `lean_goal` at L10577 to see the exact goal type
2. The goal is about steps from the OUTER expression (e.g., `.if c_flat then_ else_`).
3. Every step through `.if [·] then_ else_` corresponds to an inner step of `c_flat`.
4. The inner step preserves funcs/cs (from `hpres_c`).
5. Wrapping in `.if · then_ else_` doesn't change funcs/cs.
6. So each outer step preserves funcs/cs.

You need to prove this by induction on the steps, using `step?_if_cond_step` to relate outer steps to inner steps.

**If this is too complex, add a general `Steps_ctx_pres` lemma near L1885 that proves:**
```lean
∀ (wrap : Flat.Expr → Flat.Expr)
  (single_step_pres : ...) -- each ctx step preserves funcs/cs
  (hpres_inner : ...) -- inner steps preserve funcs/cs
  → wrapped steps also preserve funcs/cs
```

## PRIORITY 2: Exotic cases (L10729, L10933) — likely contradictions
```lean
lean_multi_attempt at L10729
["next hif => cases hif", "intro hif; cases hif"]
```
If HasIfInHead doesn't apply to binary/unary/getProp/etc., `cases hif` closes the goal.

## PRIORITY 3: seq_right (L10632, L10836)
Use `Classical.em (HasIfInHead a)`:
- HasIfInHead a: IH on a
- ¬HasIfInHead a: `trivialChain_eval_value` on a, then IH on b

## PRIORITY 4: trivialChain eval (L10585, L10791)
Use `trivialChain_if_true_sim` / `trivialChain_if_false_sim` directly.

## USE lean_multi_attempt AGGRESSIVELY
Before editing, test tactics at each sorry. This avoids rebuilds.

## PRIORITY ORDER: hpres → exotic → seq_right → trivialChain → false mirror

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
