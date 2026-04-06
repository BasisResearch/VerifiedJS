# proof — Refactor throw/return/await/yield to depth induction

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~1.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13901+ and L14996+ zones (if_branch individual cases)
- jsspec may work on ClosureConvertCorrect.lean
- **YOU** own throw/return/await/yield step_sim AND compound zones AND while/tryCatch/callframe/break
- DO NOT touch wasmspec or jsspec zones

## ===== THE KEY INSIGHT: COMPOUND CASES NEED DEPTH INDUCTION =====

**Root cause of all 11 compound sorries**: `normalizeExpr_throw_step_sim` (L11568), `normalizeExpr_return_step_sim` (L11700), `normalizeExpr_await_step_sim` (L11884), and `normalizeExpr_yield_step_sim` (L12034) are **standalone theorems without induction**. Their compound cases (HasThrowInHead seq_left, let_init, etc.) need recursive calls on sub-expressions, but there's no IH available.

**The fix**: Refactor these 4 theorems to use **depth induction**, exactly like `normalizeExpr_if_branch_step` (L13034) and `normalizeExpr_labeled_step_sim` (L10455) already do.

### Template from if_branch_step (L13034):
```lean
private theorem normalizeExpr_if_branch_step :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    HasIfInHead e →
    ∀ (env : Flat.Env) ... :=  by
  intro d; induction d with
  | zero => ... -- impossible: depth 0 can't have HasIfInHead
  | succ d ih => ...
    -- For compound cases like seq_left:
    -- have h_sub_depth : sub.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
    -- obtain ⟨...⟩ := ih sub h_sub_depth h_sub_if env ...
    -- lift steps through eval context
```

## ===== P0: REFACTOR normalizeExpr_throw_step_sim (1 sorry → depth induction) =====

Current signature (L11568):
```lean
private theorem normalizeExpr_throw_step_sim
    (sf : Flat.State) (k : ...) (arg : ANF.Trivial) (n m : Nat)
    (hnorm : ...) (hk : ...) (hewf : ...) (hna : ...) :
```

Refactor to:
```lean
private theorem normalizeExpr_throw_step_sim :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    HasThrowInHead e →
    ∀ (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
      (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat),
    (∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m')) →
    (ANF.normalizeExpr e k).run n = .ok (.throw arg, m) →
    ExprWellFormed e env →
    NoNestedAbrupt e →
    -- ok case + error case conclusions
```

### Steps:
1. Change the signature to take `(d : Nat) (e : Flat.Expr), e.depth ≤ d → HasThrowInHead e →`
2. Move `intro d; induction d` at the top
3. `zero` case: impossible (no HasThrowInHead at depth 0) — prove by cases on e
4. `succ d ih` case: keep ALL existing base case proofs (lit, var, this, break, continue)
5. For the catch-all compound case at L11694-11696, case-split on HasThrowInHead:
   - For each compound constructor (e.g., `seq_left`): extract sub_depth, apply `ih`, lift through context using existing `Steps_*_ctx_b` lemmas
6. Update ALL call sites of normalizeExpr_throw_step_sim to pass `e.depth` and `Nat.le_refl _`

### The compound case template:
```lean
| HasThrowInHead.seq_left a b h_a =>
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run, Except.bind] at hnorm
  have ha_depth : a.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
  -- normalizeExpr (.seq a b) k = normalizeExpr a (fun _ => normalizeExpr b k)
  -- So hnorm says normalizeExpr a (...) = .ok (.throw arg, m)
  -- The throw propagates from a's normalization
  obtain ⟨ok_case, err_case⟩ := ih a ha_depth h_a env heap trace funcs cs _ arg _ m _ hnorm' hewf_a hna_a
  -- Lift through seq context
  ...
```

**Do the throw case FIRST. If it works, apply the same pattern to return/await/yield.**

## P1: While + tryCatch + callframe + break/continue (9 sorries)
After completing P0, these may become tractable.

```
L12339: sorry -- While condition value case
L12351: sorry -- Condition-steps case
L16349: sorry -- tryCatch body-error
L16367: sorry -- tryCatch body-step
L16370: | _ => sorry -- compound cases: deferred
L17453: sorry -- noCallFrameReturn
L17464: sorry -- body_sim IH
L17684: sorry -- break
L17737: sorry -- continue
```

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
