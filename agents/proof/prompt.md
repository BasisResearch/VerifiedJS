# proof — Build HasAwaitInHead infrastructure, then prove await_step_sim

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 18 sorries. Lower 0 ✓. CC ~19 — OTHER AGENTS OWN IT.

## WHY GROUP B IS BLOCKED (DO NOT ATTEMPT)
Your previous analysis (correct): GROUP B sorries (L3857, L3888, L3977, L4008) need the IH
with non-trivial continuations like `fun t => pure (.return (some t))`. The IH at L3668
requires `hk : ∀ arg n', ∃ m', (k arg).run n' = .ok (.trivial arg, m')` — forces k to produce
`.trivial`. Generalizing this is blocked because the OUTPUT k' (L3674-3675) must also be
trivial-preserving (required by anfConvert_step_star at L4682 for ANF_SimRel). Skip GROUP B.

## YOUR TASK: Build HasAwaitInHead + prove normalizeExpr_await_step_sim

This follows the EXACT pattern of HasThrowInHead (L3224) + normalizeExpr_throw_or_k (L3371) +
normalizeExpr_throw_implies_hasThrowInHead (L3647) + normalizeExpr_throw_step_sim (L4098).

### Step 1: Define HasAwaitInHead (insert BEFORE L4257)

Copy HasThrowInHead (L3224-3268), but:
- Replace `throw_direct` with `await_direct : HasAwaitInHead (.await arg)`
- Keep ALL other constructors identical (seq_left, seq_right, let_init, getProp_obj, etc.)
- Copy HasAwaitInHeadList and HasAwaitInHeadProps too

```lean
/-! ## HasAwaitInHead mutual inductive -/

set_option autoImplicit true in
mutual
inductive HasAwaitInHead : Flat.Expr → Prop where
  | await_direct : HasAwaitInHead (.await arg)
  | seq_left : HasAwaitInHead a → HasAwaitInHead (.seq a b)
  | seq_right : HasAwaitInHead b → HasAwaitInHead (.seq a b)
  | let_init : HasAwaitInHead init → HasAwaitInHead (.let name init body)
  | getProp_obj : HasAwaitInHead obj → HasAwaitInHead (.getProp obj prop)
  | setProp_obj : HasAwaitInHead obj → HasAwaitInHead (.setProp obj prop val)
  | setProp_val : HasAwaitInHead val → HasAwaitInHead (.setProp obj prop val)
  | binary_lhs : HasAwaitInHead lhs → HasAwaitInHead (.binary op lhs rhs)
  | binary_rhs : HasAwaitInHead rhs → HasAwaitInHead (.binary op lhs rhs)
  | unary_arg : HasAwaitInHead arg → HasAwaitInHead (.unary op arg)
  | typeof_arg : HasAwaitInHead arg → HasAwaitInHead (.typeof arg)
  | deleteProp_obj : HasAwaitInHead obj → HasAwaitInHead (.deleteProp obj prop)
  | assign_val : HasAwaitInHead val → HasAwaitInHead (.assign name val)
  | call_func : HasAwaitInHead f → HasAwaitInHead (.call f env args)
  | call_env : HasAwaitInHead env → HasAwaitInHead (.call f env args)
  | call_args : HasAwaitInHeadList args → HasAwaitInHead (.call f env args)
  | newObj_func : HasAwaitInHead f → HasAwaitInHead (.newObj f env args)
  | newObj_env : HasAwaitInHead env → HasAwaitInHead (.newObj f env args)
  | newObj_args : HasAwaitInHeadList args → HasAwaitInHead (.newObj f env args)
  | if_cond : HasAwaitInHead c → HasAwaitInHead (.if c t e)
  | throw_arg : HasAwaitInHead arg → HasAwaitInHead (.throw arg)
  | return_some_arg : HasAwaitInHead v → HasAwaitInHead (.return (some v))
  | yield_some_arg : HasAwaitInHead v → HasAwaitInHead (.yield (some v) d)
  | getIndex_obj : HasAwaitInHead obj → HasAwaitInHead (.getIndex obj idx)
  | getIndex_idx : HasAwaitInHead idx → HasAwaitInHead (.getIndex obj idx)
  | setIndex_obj : HasAwaitInHead obj → HasAwaitInHead (.setIndex obj idx val)
  | setIndex_idx : HasAwaitInHead idx → HasAwaitInHead (.setIndex obj idx val)
  | setIndex_val : HasAwaitInHead val → HasAwaitInHead (.setIndex obj idx val)
  | getEnv_env : HasAwaitInHead env → HasAwaitInHead (.getEnv env idx)
  | makeClosure_env : HasAwaitInHead env → HasAwaitInHead (.makeClosure funcIdx env)
  | makeEnv_values : HasAwaitInHeadList values → HasAwaitInHead (.makeEnv values)
  | objectLit_props : HasAwaitInHeadProps props → HasAwaitInHead (.objectLit props)
  | arrayLit_elems : HasAwaitInHeadList elems → HasAwaitInHead (.arrayLit elems)

inductive HasAwaitInHeadList : List Flat.Expr → Prop where
  | head : HasAwaitInHead e → HasAwaitInHeadList (e :: rest)
  | tail : HasAwaitInHeadList rest → HasAwaitInHeadList (e :: rest)

inductive HasAwaitInHeadProps : List (Flat.PropName × Flat.Expr) → Prop where
  | head : HasAwaitInHead e → HasAwaitInHeadProps ((name, e) :: rest)
  | tail : HasAwaitInHeadProps rest → HasAwaitInHeadProps (p :: rest)
end
```

**BUILD after this step.**

### Step 2: Write normalizeExpr_await_or_k (insert after HasAwaitInHead)

Copy normalizeExpr_throw_or_k_aux (L3379-3646) and normalizeExpr_throw_or_k (L3371-3376).
Replace `.throw` → `.await`, `HasThrowInHead` → `HasAwaitInHead`, `throw_direct` → `await_direct`.

Key changes per case in the aux:
- `.await arg_flat` → `exact Or.inl HasAwaitInHead.await_direct` (was .throw)
- `.throw arg_flat` → since normalizeExpr (.throw arg) k ignores k and produces .throw,
  if result is .await, need ih on arg. Same depth argument as throw handled .await in throw version.

Actually: in throw_or_k, the `.await _` case at L3416 says `simp [Flat.Expr.depth] at hd` (depth
too large for zero). For await_or_k:
- `.await arg` case: `exact Or.inl HasAwaitInHead.await_direct` (this is the direct case)
- `.throw arg` case: normalizeExpr (.throw arg) k = normalizeExpr arg (fun t => pure (.throw t)).
  If result is .await, then `(fun t => pure (.throw t))` produced .await for some arg, which is
  impossible (it produces .throw). So `ih` on arg gives `HasAwaitInHead arg`, giving
  `HasAwaitInHead (.throw arg)` via `.throw_arg`.

The structure is IDENTICAL to throw_or_k with throw↔await swapped. Copy mechanically.

**BUILD after this step.**

### Step 3: Write normalizeExpr_await_implies_hasAwaitInHead (10 lines)

```lean
theorem ANF.normalizeExpr_await_implies_hasAwaitInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.await arg, m)) :
    HasAwaitInHead e := by
  rcases ANF.normalizeExpr_await_or_k e k arg n m h with hleft | ⟨t, n', m', hk_await⟩
  · exact hleft
  · obtain ⟨m'', hm''⟩ := hk t n'
    rw [hm''] at hk_await
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_await)).1
```

**BUILD after this step.**

### Step 4: Prove normalizeExpr_await_step_sim base cases

Follow normalizeExpr_throw_step_sim (L4098-4222). Structure:
1. Use `normalizeExpr_await_implies_hasAwaitInHead` to get `HasAwaitInHead sf.expr`
2. `cases sf; simp at *`
3. `cases hhas : HasAwaitInHead` (the head structure)
4. For `await_direct` (sf.expr = .await flat_arg):
   - normalizeExpr (.await flat_arg) k = normalizeExpr flat_arg (fun t => pure (.await t))
   - Case split flat_arg: lit, var, this (base cases), break/continue (contradiction)
   - Each base case: construct Flat steps for await resolution
   - Compound flat_arg: sorry (same as throw L4219)
5. For all other HasAwaitInHead constructors: sorry (compound evaluation context)

**The goal is to replace 1 sorry (L4277) with ~2 sorries (compound cases) + proven base cases.**
Even if net sorry count stays same, this is STRUCTURAL PROGRESS needed for the end-to-end proof.

## WORKFLOW
1. `grep -n "sorry" VerifiedJS/Proofs/ANFConvertCorrect.lean` to confirm line numbers
2. Add HasAwaitInHead inductive BEFORE normalizeExpr_await_step_sim
3. Build
4. Add normalizeExpr_await_or_k_aux + normalizeExpr_await_or_k
5. Build
6. Add normalizeExpr_await_implies_hasAwaitInHead
7. Build
8. Start normalizeExpr_await_step_sim proof
9. Build
10. Log to agents/proof/log.md after each step

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
