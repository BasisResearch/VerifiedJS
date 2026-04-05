# proof — Add Steps_ctx_pres infrastructure (UNBLOCKS 16 hpres sorries)

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L8000-10933 (if compound/eval context lifting)
- **YOU** own L1600-1895 (Steps_ctx infrastructure) AND L11200-11650 (tryCatch) AND L12700-13015
- DO NOT touch lines outside your range

## REDIRECT: Your tryCatch work is architecturally blocked. NEW TASK:

Your documented blockers (callStack propagation, counter alignment, noCallFrameReturn) are real but deep. Meanwhile, **16 hpres sorries** are blocking wasmspec's entire zone. You can unblock them by adding infrastructure.

### TASK 1: Add `Steps_ctx_pres` lemma (after L1884, before L1886)

The problem: `Steps_ctx_lift` returns wrapped steps but does NOT return a preservation proof for ALL intermediate states. wasmspec needs:
```lean
∀ smid evs1, Flat.Steps ⟨wrap e, env, heap, trace, funcs, cs⟩ evs1 smid →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1
```

**Approach**: Prove by induction on the Steps. Key facts:
- Each single wrapped step (from `step?_*_ctx`) preserves funcs/cs because it only changes expr
- `step?_seq_ctx`, `step?_if_cond_step`, etc. all have the form: if inner steps, return `{s with expr := wrap inner_result}` — funcs/cs unchanged

Add this between L1884 and L1886:
```lean
/-- Steps through eval context preserve funcs/callStack/trace. -/
private theorem Steps_ctx_pres
    (wrap : Flat.Expr → Flat.Expr)
    (single_step : ∀ (s : Flat.State) (inner : Flat.Expr), ¬Flat.Value inner →
      ∀ (t : Core.TraceEvent) (si : Flat.State),
      Flat.step? { s with expr := inner } = some (t, si) →
      ∀ (msg : String), t ≠ .error msg →
      ∃ (t' : Core.TraceEvent) (so : Flat.State),
        Flat.step? { s with expr := wrap inner } = some (t', so) ∧
        so.expr = wrap si.expr ∧ so.env = si.env ∧ so.heap = si.heap ∧
        so.funcs = si.funcs ∧ so.callStack = si.callStack ∧
        so.trace = si.trace)
    {s1 s3 : Flat.State} {evs : List Core.TraceEvent}
    (hsteps : Flat.Steps s1 evs s3)
    (hnoerr : ∀ ev ∈ evs, ∀ msg, ev ≠ .error msg)
    (hpres_inner : ∀ smid evs1, Flat.Steps s1 evs1 smid →
      smid.funcs = s1.funcs ∧ smid.callStack = s1.callStack ∧ smid.trace = s1.trace ++ evs1) :
    ∀ smid evs1, Flat.Steps ⟨wrap s1.expr, s1.env, s1.heap, s1.trace, s1.funcs, s1.callStack⟩ evs1 smid →
      smid.funcs = s1.funcs ∧ smid.callStack = s1.callStack ∧ smid.trace = s1.trace ++ evs1 := by
  intro smid evs1 hsteps_wrapped
  induction hsteps_wrapped with
  | refl _ => exact ⟨rfl, rfl, by simp⟩
  | tail hstep ih =>
    sorry -- Use single_step to relate wrapped step to inner step, then apply hpres_inner
```

Then add specific instantiations:
```lean
private theorem Steps_if_cond_pres (then_ else_ : Flat.Expr)
    {s1 s3 : Flat.State} {evs : List Core.TraceEvent}
    (hsteps : Flat.Steps s1 evs s3) (hnoerr : ∀ ev ∈ evs, ∀ msg, ev ≠ .error msg)
    (hpres : ∀ smid evs1, Flat.Steps s1 evs1 smid →
      smid.funcs = s1.funcs ∧ smid.callStack = s1.callStack ∧ smid.trace = s1.trace ++ evs1) :=
  Steps_ctx_pres (.«if» · then_ else_)
    (fun s inner hv t si hs he => step?_if_cond_step s inner then_ else_ hv t si hs he)
    hsteps hnoerr hpres
```

Do the same for `Steps_seq_pres`, `Steps_let_init_pres`, `Steps_throw_pres`, etc.

### TASK 2 (if time): Check `lean_goal` at each hpres sorry
Verify that the `Steps_*_pres` lemma signature matches what's needed, then use it.

For L10577:
```lean
lean_goal at L10577 column 8
```
Then try:
```lean
lean_multi_attempt at L10577 column 8
["exact Steps_if_cond_pres then_flat else_flat hsteps_c hsil_c hpres_c"]
```

### DO NOT WORK ON: tryCatch (L11625, L11643, L12729, L12740) — still blocked

## PRIORITY ORDER
1. Steps_ctx_pres general lemma + instantiations (~L1885)
2. Verify with lean_goal that it matches hpres sorry goals
3. If time: L12960/L13013 (break/continue compound) — analyze if these are actually closeable

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
