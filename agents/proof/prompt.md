# proof — Decompose L9178 NoNestedAbrupt_step_preserved into per-constructor cases

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## STATE: You successfully extracted NoNestedAbrupt_step_preserved as a standalone lemma at L9175. GOOD. Now FILL IT IN.

## TASK (DO THIS NOW): Replace the sorry at L9178 with the full case split

The current code at L9175-9178:
```lean
private theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr) (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr := by
  sorry
```

### STEP 1: Write hasAbruptCompletion_step_preserved helper

Insert this BEFORE L9174 (before the `/-- Flat single-step preserves NoNestedAbrupt` doc comment):

```lean
private theorem hasAbruptCompletion_step_preserved (e : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env) (ev : Core.TraceEvent) (sf' : Flat.State)
    (hac : hasAbruptCompletion e = false)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf')) :
    hasAbruptCompletion sf'.expr = false := by
  sorry -- SEPARATE THEOREM: prove later by same induction pattern
```

### STEP 2: Replace L9178 sorry with full skeleton

Replace `sorry` at L9178 with EXACTLY this code:

```lean
  obtain ⟨expr, env, heap, trace, funcs, cs⟩ := sf
  simp only [Flat.State.expr] at hna
  suffices ∀ n e, e.depth ≤ n → ∀ env heap trace funcs cs ev sf',
    NoNestedAbrupt e →
    Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf') →
    NoNestedAbrupt sf'.expr from this _ _ (le_refl _) _ _ _ _ _ hna hstep
  intro n
  induction n with
  | zero => intro e hd; cases e <;> simp [Flat.Expr.depth] at hd <;> omega
  | succ n ih =>
    intro e hd env heap trace funcs cs ev sf' hna hstep
    cases e with
    -- DOES NOT STEP (step? = none → contradicts hstep)
    | lit v => simp [Flat.step?] at hstep
    -- SIMPLE: steps to .lit → NoNestedAbrupt.lit
    | var name =>
      simp [Flat.step?] at hstep
      split at hstep <;> simp [Flat.pushTrace] at hstep <;> obtain ⟨_, rfl⟩ := hstep <;> exact NoNestedAbrupt.lit
    | this =>
      simp [Flat.step?] at hstep
      split at hstep <;> simp [Flat.pushTrace] at hstep <;> obtain ⟨_, rfl⟩ := hstep <;> exact NoNestedAbrupt.lit
    | break label =>
      simp [Flat.step?] at hstep; simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact NoNestedAbrupt.lit
    | continue label =>
      simp [Flat.step?] at hstep; simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact NoNestedAbrupt.lit
    -- VACUOUSLY TRUE: no NoNestedAbrupt constructor exists
    | unary op arg => cases hna
    | binary op l r => cases hna
    | while_ cond body => cases hna
    | labeled label body => cases hna
    -- MEDIUM: context-stepping with IH
    | seq a b =>
      cases hna with | seq ha hb =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact hb
      case h_2 hv =>
        split at hstep
        case h_1 ev' sa hsa =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.seq
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ ha hsa) hb
        case h_2 => simp at hstep
    | «let» name init body =>
      cases hna with | «let» hinit hbody =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact hbody
      case h_2 hv =>
        split at hstep
        case h_1 ev' si hsi =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.let
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hinit hsi) hbody
        case h_2 => simp at hstep
    | assign name rhs =>
      cases hna with | assign hrhs =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_2 hv =>
        split at hstep
        case h_1 ev' sr hsr =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.assign
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hrhs hsr)
        case h_2 => simp at hstep
    | «if» cond then_ else_ =>
      cases hna with | «if» hc hthen helse =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; split <;> assumption
      case h_2 hv =>
        split at hstep
        case h_1 ev' sc hsc =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.if
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hc hsc) hthen helse
        case h_2 => simp at hstep
    -- THROW/RETURN/AWAIT/YIELD: use hasAbruptCompletion_step_preserved
    | throw arg =>
      cases hna with | throw habr =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_2 hv =>
        split at hstep
        case h_1 ev' sa hsa =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.throw (hasAbruptCompletion_step_preserved arg env heap trace funcs cs ev' sa habr hsa)
        case h_2 => simp at hstep
    | «return» arg =>
      cases hna with
      | return_none =>
        simp [Flat.step?] at hstep; simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      | return_some habr =>
        simp [Flat.step?] at hstep
        split at hstep
        case h_1 v hv =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]; exact NoNestedAbrupt.lit
        case h_2 hv =>
          split at hstep
          case h_1 ev' se hse =>
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
            simp [Flat.State.expr]
            exact NoNestedAbrupt.return_some (hasAbruptCompletion_step_preserved _ _ _ _ _ _ _ _ habr hse)
          case h_2 => simp at hstep
    | await arg =>
      cases hna with | await habr =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_2 hv =>
        split at hstep
        case h_1 ev' sa hsa =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.await (hasAbruptCompletion_step_preserved _ _ _ _ _ _ _ _ habr hsa)
        case h_2 => simp at hstep
    | yield arg d =>
      cases hna with
      | yield_none =>
        simp [Flat.step?] at hstep; simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      | yield_some habr =>
        simp [Flat.step?] at hstep
        split at hstep
        case h_1 v hv =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]; exact NoNestedAbrupt.lit
        case h_2 hv =>
          split at hstep
          case h_1 ev' se hse =>
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
            simp [Flat.State.expr]
            exact NoNestedAbrupt.yield_some (hasAbruptCompletion_step_preserved _ _ _ _ _ _ _ _ habr hse)
          case h_2 => simp at hstep
    -- COMPLEX: multi-sub-expression stepping — sorry for now
    | getProp obj prop =>
      cases hna with | getProp hobj =>
      simp [Flat.step?] at hstep
      sorry
    | setProp obj prop val =>
      cases hna with | setProp hobj hval =>
      simp [Flat.step?] at hstep
      sorry
    | getIndex obj idx =>
      cases hna with | getIndex hobj hidx =>
      simp [Flat.step?] at hstep
      sorry
    | setIndex obj idx val =>
      cases hna with | setIndex hobj hidx hval =>
      simp [Flat.step?] at hstep
      sorry
    | deleteProp obj prop =>
      cases hna with | deleteProp hobj =>
      simp [Flat.step?] at hstep
      sorry
    | typeof arg =>
      cases hna with | typeof harg =>
      simp [Flat.step?] at hstep
      sorry
    | call f fenv args =>
      cases hna with | call hf henv hargs =>
      simp [Flat.step?] at hstep
      sorry
    | newObj f fenv args =>
      cases hna with | newObj hf henv hargs =>
      simp [Flat.step?] at hstep
      sorry
    | getEnv envExpr idx =>
      cases hna with | getEnv henv =>
      simp [Flat.step?] at hstep
      sorry
    | makeEnv vals =>
      cases hna with | makeEnv hvals =>
      simp [Flat.step?] at hstep
      sorry
    | makeClosure funcIdx envExpr =>
      cases hna with | makeClosure henv =>
      simp [Flat.step?] at hstep
      sorry
    | objectLit props =>
      cases hna with | objectLit hprops =>
      simp [Flat.step?] at hstep
      sorry
    | arrayLit elems =>
      cases hna with | arrayLit helems =>
      simp [Flat.step?] at hstep
      sorry
    | tryCatch body param catchBody fin =>
      cases hna with
      | tryCatch_some hbody hcatch hfin => sorry
      | tryCatch_none hbody hcatch => sorry
```

### IMPORTANT NOTES ON THE SKELETON:
- The `ih` call uses `ih _` not `ih n` — the underscore lets Lean infer the nat argument
- `hasAbruptCompletion_step_preserved` will be defined with sorry body — that's fine, it moves sorries to a separate theorem
- After this, L9178 goes from 1 sorry → ~16 smaller sorries (1 for hasAbruptCompletion + 15 complex cases)
- This is PROGRESS because each sorry is now isolated and self-contained

### STEP 3: Try closing easy complex cases

After skeleton compiles, try closing `getProp` (single sub-expr, same pattern as `assign`):
```lean
    | getProp obj prop =>
      cases hna with | getProp hobj =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv => -- exprValue? obj = some v → .lit result
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_2 hv =>
        split at hstep
        case h_1 ev' so hso =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.getProp
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hobj hso)
        case h_2 => simp at hstep
```

Same pattern works for `deleteProp` and `typeof`.

## DO NOT:
- Work on Group A (L7516-7702) — PARKED
- Work on L8850 (let), L8898 (while), L9063/9064/9129/9130 (if) — wasmspec handles
- Work on L8343 (compound throw dispatch) — DEFERRED
- Work on L9174 (tryCatch) — DEFERRED
- Work on L9571/L9624 (break/continue) — PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
