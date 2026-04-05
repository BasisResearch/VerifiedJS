# wasmspec — FIX hpres BUG (16 sorries), then exotic/seq_right

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
- **YOU** own L1767-1895 (Steps_ctx_lift infrastructure) AND L8000-11110 (normalizeExpr step sim)
- DO NOT touch lines outside your range

## CRITICAL BUG: hpres is UNPROVABLE as currently stated

The hpres output in `normalizeExpr_if_branch_step` (L10708-10709) claims:
```lean
(∀ smid evs1, Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs1 smid →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1)
```

This is **FALSE**. After `.if c then else` evaluates c to a value and branches to `then`, subsequent steps in `then` can change callStack (if `then` contains `.call`). The universal quantifier over ALL step sequences makes this unprovable.

### THE FIX: Bounded hpres

Change to:
```lean
(∀ smid evs1, Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs1 smid →
    evs1.length ≤ evs.length →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1)
```

The bound `evs1.length ≤ evs.length` restricts to steps within the condition evaluation phase (before branching), where funcs/cs ARE preserved.

### STEP 1: Modify Steps_ctx_lift (L1781)

Change the `hpres` parameter at L1781-1783 from:
```lean
(hpres : ∀ (smid : Flat.State) (evs1 : List Core.TraceEvent),
   Flat.Steps s1 evs1 smid →
   smid.funcs = s1.funcs ∧ smid.callStack = s1.callStack ∧ smid.trace = s1.trace ++ evs1)
```
to:
```lean
(hpres : ∀ (smid : Flat.State) (evs1 : List Core.TraceEvent),
   Flat.Steps s1 evs1 smid → evs1.length ≤ evs.length →
   smid.funcs = s1.funcs ∧ smid.callStack = s1.callStack ∧ smid.trace = s1.trace ++ evs1)
```

Then fix the proof:
- At L1797: `have hs2_pres := hpres s2 [t] (.tail hstep (.refl _)) (by simp)`
  The `by simp` proves `[t].length ≤ (t :: ts).length`, i.e., `1 ≤ 1 + ts.length`.
- At L1806: `have h := hpres smid (t :: evs1) (.tail hstep hsteps_s2) (by omega)`
  Add `(hlen_s2 : evs1.length ≤ ts.length)` to the intro of hpres_s2 and use `by omega` to prove `(t :: evs1).length ≤ (t :: ts).length`.

The full modified hpres_s2 derivation (L1803-1808):
```lean
have hpres_s2 : ∀ smid evs1, Flat.Steps s2 evs1 smid → evs1.length ≤ ts.length →
    smid.funcs = s2.funcs ∧ smid.callStack = s2.callStack ∧ smid.trace = s2.trace ++ evs1 := by
  intro smid evs1 hsteps_s2 hlen_s2
  have h := hpres smid (t :: evs1) (.tail hstep hsteps_s2) (by omega)
  exact ⟨h.1.trans hs2f.symm, h.2.1.trans hs2c.symm,
         by rw [h.2.2, hs2t, List.append_assoc]; rfl⟩
```

### STEP 2: Update all Steps_*_ctx wrappers (L1819-1884)

Each wrapper (Steps_seq_ctx, Steps_throw_ctx, Steps_let_init_ctx, Steps_if_cond_ctx, Steps_return_some_ctx, Steps_yield_some_ctx, Steps_await_ctx) needs its hpres parameter updated to include `evs1.length ≤ evs.length →`. Mechanical change — just add the bound to each hpres type.

Also update Steps_unary_ctx and Steps_binary_lhs_ctx if they exist (you added them).

### STEP 3: Update normalizeExpr_if_branch_step output type (L10708)

Change:
```lean
(∀ smid evs1, Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs1 smid →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1) ∧
```
to:
```lean
(∀ smid evs1, Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs1 smid →
    evs1.length ≤ evs.length →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1) ∧
```

Do the same for `normalizeExpr_if_branch_step_false` (L10905+).

### STEP 4: Close the 16 hpres sorries

At each hpres sorry (L10750, 10774, 10796, 10820, 10840, 10859, 10878, 10897, and 8 symmetric in false branch), the goal is now BOUNDED:
```lean
∀ smid evs1, Steps ⟨.if c_flat then_flat else_flat, ...⟩ evs1 smid →
    evs1.length ≤ evs_c.length →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1
```

**Proof strategy**: By induction on `hmid : Steps ... evs1 smid`, using determinism with the constructed `hwsteps`:

```lean
· -- bounded hpres
  intro smid evs1 hmid hlen
  induction hmid with
  | refl _ => exact ⟨rfl, rfl, by simp⟩
  | @tail _ ws2' _ t' ts' hstep' hrest' ih_mid =>
    -- From construction: step? ws1 = some (t0, ws2)
    -- From hstep': step? ws1 = some (t', ws2')
    -- ws1 is the same state → determinism gives t' = t0 and ws2' = ws2
    have hdet : (t', ws2') = (t0, ws2) := by
      have h1 := hwstep  -- the constructed first step equation
      rw [h1] at hstep'.1; exact (Option.some.inj hstep'.1).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hdet.symm
    -- ws2.funcs = s1.funcs (from single_step output: hwfuncs)
    -- IH on rest with bound |ts'| ≤ |evs_c| - 1
    -- Need to relate IH to the remaining constructed steps
    sorry -- details depend on exact proof structure
```

**SIMPLER alternative**: If the induction is too complex, prove a general lemma first:

```lean
/-- step? on .if always preserves funcs and callStack -/
private theorem step?_if_preserves (c then_ else_ : Flat.Expr) (s : Flat.State) (t : Core.TraceEvent) (s' : Flat.State)
    (h : Flat.step? { s with expr := .if c then_ else_ } = some (t, s')) :
    s'.funcs = s.funcs ∧ s'.callStack = s.callStack := by
  simp [Flat.step?] at h
  split at h <;> simp_all [Flat.step?_pushTrace_expand]
  all_goals exact ⟨rfl, rfl⟩  -- each case just changes expr/trace
```

Then use:
```lean
/-- Steps that only go through eval-context states preserve funcs/cs -/
-- Use Steps_inv_all pattern with P = (funcs = F ∧ cs = CS ∧ ∃ c, expr = .if c then_ else_)
```

BUT: after branching the .if form is lost. Since we now have the bound, the branching step doesn't happen within the bound. Prove this using determinism: Steps of length ≤ |evs_c| from the same start must be prefixes of hwsteps, and hwsteps only has condition-evaluation steps.

**USE lean_multi_attempt AGGRESSIVELY** to test approaches before editing.

### STEP 5: Update call sites of Steps_*_ctx

Each call site (like L10744-10747) passes `hpres_c` to `Steps_if_cond_ctx`. Since `hpres_c` now comes from the IH with the bounded form, and Steps_if_cond_ctx accepts bounded form, this should type-check automatically. But verify with `lean_goal`.

### STEP 6: Exotic cases (L10902, L11106) — likely contradictions

```lean
lean_multi_attempt at L10902 column 4
["cases hif", "exact absurd hif (by intro h; cases h)"]
```

If HasIfInHead doesn't apply to binary/unary/getProp/etc., `cases hif` closes the goal immediately.

### STEP 7: seq_right (L10805, L11009)

Use `Classical.em (HasIfInHead a)`:
- HasIfInHead a: IH on a
- ¬HasIfInHead a: `trivialChain_eval_value` on a, then IH on b

## PRIORITY ORDER
1. Steps_ctx_lift bounded hpres change (STEP 1-2)
2. normalizeExpr_if_branch_step output change (STEP 3)
3. Close hpres sorries (STEP 4-5) — TARGET: 16 sorries closed
4. Exotic cases (STEP 6) — TARGET: 2 more
5. seq_right (STEP 7) — TARGET: 2 more

**Expected: ANF drops by 16-20 sorries this run.**

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
