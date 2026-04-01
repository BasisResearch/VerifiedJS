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

## STATE: ANF 18 sorries (UNCHANGED 3+ RUNS). Lower 0 ✓. CC ~14 — OTHER AGENTS OWN IT.

## URGENCY: You have been stuck at 18 sorries for too long.
Even STRUCTURAL progress (decomposing 1 sorry into sub-cases with some proved) is valuable.
The HasAwaitInHead infrastructure is the RIGHT approach. If you haven't started it yet, START NOW.
If you've been investigating instead of writing code, STOP investigating and START writing.

## WHY GROUP B IS BLOCKED (DO NOT ATTEMPT)
GROUP B sorries (L3857, L3888, L3977, L4008) need the IH with non-trivial continuations.
The IH at L3668 requires trivializing k. Generalizing is blocked by output requirements.
Skip GROUP B entirely.

## YOUR TASK: Build HasAwaitInHead + prove normalizeExpr_await_step_sim

This follows the EXACT pattern of HasThrowInHead (L3224) + normalizeExpr_throw_or_k (L3371) +
normalizeExpr_throw_implies_hasThrowInHead (L3647) + normalizeExpr_throw_step_sim (L4098).

### Step 1: Define HasAwaitInHead (insert BEFORE the await_step_sim sorry)

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

Follow normalizeExpr_throw_step_sim (L4098-4222). Even if compound cases stay sorry,
this decomposes the monolithic sorry into smaller tractable pieces.

## CURRENT ANF SORRY LOCATIONS (file is 6173 lines):
```
GROUP B (SKIP): L3857, L3888, L3899, L3977, L4008, L4019, L4036
throw compound: L4053, L4066
await compound flat_arg: L4219
await/seq/if/let/tryCatch: L4222, L4253, L4277, L4308, L4329, L4350, L4371, L4392
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
