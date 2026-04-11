# proof — CLOSE HasReturnInHead_step_error_isLit (L14157)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE lemma, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T12:00
- ANF: 33 sorries. CC: 15 (jsspec). Total: 48.
- **HasReturnInHead_step_nonError WRITTEN** (wasmspec, ~600 lines) — depends on step_error_isLit
- **HasReturnInHead_Steps_steppable (L14161) PROVED** — depends on step_error_isLit
- Closing step_error_isLit cascades: -4 to -8 sorries
- **YOU HAVE BEEN WORKING ON THIS FOR 30 MIN WITH NO FILE OUTPUT. WRITE CODE NOW.**

## ⚠️ DO NOT WORK ON:
- L10429-L10800 (trivialChain — LSP TIMEOUT zone)
- L12969-L14148 (wasmspec-owned HasReturnInHead_step_nonError)
- L15033-L15810 (while/if — BLOCKED)
- L16651-L16672 (tryCatch — BLOCKED)
- L17999, L18010 (noCallFrameReturn/body_sim — BLOCKED)

## P0: HasReturnInHead_step_error_isLit (L14157) — CASCADE BLOCKER

```lean
private theorem HasReturnInHead_step_error_isLit
    {sf sf' : Flat.State} {msg : String}
    (hret : HasReturnInHead sf.expr)
    (hstep : Flat.step? sf = some (.error msg, sf')) :
    ∃ v, sf'.expr = .lit v
```

### THE PROOF — FOLLOW step_nonError PATTERN EXACTLY (L13623-13649)

Use EXACTLY the same strong induction skeleton as step_nonError:

```lean
  sorry -- REPLACE WITH:
  suffices hmain : ∀ (n : Nat) (e : Flat.Expr) (env : Flat.Env) (heap : Core.Heap)
      (trace : List Core.TraceEvent) (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
      (sf' : Flat.State) (msg : String),
      e.depth ≤ n →
      HasReturnInHead e →
      Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (.error msg, sf') →
      ∃ v, sf'.expr = .lit v by
    cases sf with | mk e env heap trace funcs cs =>
    exact hmain e.depth e env heap trace funcs cs sf' msg (Nat.le_refl _) hret hstep
  intro n
  induction n with
  | zero =>
    intro e env heap trace funcs cs sf' msg hd hret hstep
    cases hret
    next => -- return_none_direct: step? produces .error "return:undefined", sf'.expr = .lit .undefined
      unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      exact ⟨.undefined, hstep.2 ▸ rfl⟩
    all_goals (simp [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth] at hd; omega)
  | succ n ih =>
    intro e env heap trace funcs cs sf' msg hd hret hstep
    cases hret with
    | return_none_direct =>
      unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      exact ⟨.undefined, hstep.2 ▸ rfl⟩
    | return_some_direct =>
      rename_i v
      unfold Flat.step? at hstep; dsimp only [] at hstep; split at hstep
      · simp [Flat.pushTrace] at hstep; exact ⟨_, hstep.2 ▸ rfl⟩  -- value → .lit v
      · split at hstep
        · split at hstep
          · simp [Flat.pushTrace] at hstep; exact ⟨_, hstep.2 ▸ rfl⟩  -- error from sub → .lit
          · -- non-error step → produces non-error event, contradicts .error msg
            simp at hstep
        · simp at hstep
    | seq_left h =>
      have hv := HasReturnInHead_not_value _ h
      unfold Flat.step? at hstep; dsimp only [] at hstep
      rw [show Flat.exprValue? _ = none from hv] at hstep; dsimp only [] at hstep
      split at hstep
      · split at hstep
        · -- error from sub-step: sf'.expr = si.expr, by IH ∃ v, si.expr = .lit v
          simp [Flat.pushTrace] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          simp only [Flat.pushTrace, Flat.State.expr]
          exact ih _ _ _ _ _ _ _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) h (by assumption)
        · -- non-error step produces (.error msg, sf') — contradiction
          sorry -- split on event type, non-error branch contradicts hstep producing .error
      · simp at hstep
    -- CONTINUE for each HasReturnInHead constructor following this EXACT pattern
    -- For seq_right: exprValue? a splits. If some: step? gives (.silent, {expr:=b}), contradiction.
    --   If none: step? sub gives IH.
    -- For EVERY compound constructor: sub-step error case gives IH, non-error gives contradiction.
    | _ => sorry -- fill in remaining cases one by one
```

### KEY FACTS FROM Flat.step? (Flat/Semantics.lean)

1. **Error propagation pattern** (ALL compound constructors): When sub-step produces `.error`:
   ```
   let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
   ```
   So `sf'.expr = si.expr`. By IH on sub-expression (depth decreases), `∃ v, si.expr = .lit v`. ✓

2. **Non-error sub-step**: Produces a non-.error event. If hstep says event is `.error msg`, contradiction.

3. **Direct error producers** (all produce `.lit v`):
   - `.return none` → `expr := .lit .undefined` ✓
   - `.return (some v)` when v is value → `expr := .lit v` ✓
   - `.throw arg` when arg is value → `expr := .lit .undefined` ✓
   - `.var name` → `expr := .lit .undefined` ✓ (but HasReturnInHead has no var constructor)
   - `.getEnv envExpr idx` → `expr := .lit .undefined` ✓
   - `.makeClosure idx envExpr` → `expr := .lit .undefined` ✓
   - `.break`/`.continue` → `expr := .lit .undefined` ✓ (but no HasReturnInHead constructor)

4. **tryCatch catch handler**: The ONLY case where error produces non-lit expr. But **HasReturnInHead has NO tryCatch constructor**, so this case is impossible.

### APPROACH: Write it in 3 BATCHES

**Batch 1**: return_none, return_some, seq_left, seq_right, let_init. Write and verify with lean_multi_attempt.
**Batch 2**: Remaining "single sub-expr" constructors (getProp_obj, setProp_obj/val, unary_arg, typeof_arg, etc.)
**Batch 3**: Multi-operand constructors (call_func/env/args, newObj, binary, getIndex, setIndex, objectLit, arrayLit, makeEnv)

### CRITICAL: The non-error branch contradiction

In compound cases, when the sub-step is non-error, step? wraps the result in the same constructor. The outer event is NOT `.error`. But `hstep` says it IS `.error msg`. This is a direct contradiction via `match t with | .error _ => ... | _ => ...` — the non-error branch produces a non-error event, contradicting `hstep`.

Tactic for this contradiction:
```lean
· -- non-error branch: event is not .error
  rename_i t_inner si hstep_inner
  split at hstep  -- on match t_inner with | .error _ => ... | _ => ...
  · sorry  -- this was the error case, handled above
  · simp [Flat.pushTrace] at hstep; -- hstep : (non-error-event, ...) = (.error msg, sf')
    exact absurd hstep.1.symm (by intro h; cases h)  -- or: injection hstep.1
```

## P1: After step_error_isLit, work on L4671 and L5809 (break/continue non-head cases)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — step_error_isLit BATCH WRITE" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
