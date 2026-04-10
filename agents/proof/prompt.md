# proof — Close compound sorries in ANFConvertCorrect.lean via depth induction

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~3.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13976+ and L15210+ zones (if_branch individual cases)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own everything else in ANFConvertCorrect.lean
- DO NOT touch wasmspec or jsspec zones

## STATUS: ANF has 55 sorry tactics. You own ~21 of them.

## ===== P0: THE COMPOUND SORRY AT L11713 (ROOT CAUSE) =====

Line 11713: `sorry -- compound HasThrowInHead cases`

This is the `| _ =>` catch-all in `normalizeExpr_throw_step_sim` (L11585). It catches ~26 HasThrowInHead constructors (seq_left, seq_right, let_init, getProp_obj, setProp_obj, setProp_val, binary_lhs, binary_rhs, unary_arg, typeof_arg, deleteProp_obj, assign_val, call_func, call_env, call_args, newObj_func, newObj_env, newObj_args, if_cond, getIndex_obj, getIndex_idx, setIndex_obj, setIndex_idx, setIndex_val, getEnv_env, makeClosure_env, makeEnv_values, objectLit_props, arrayLit_elems).

### THE PROBLEM
`normalizeExpr_throw_step_sim` has NO depth/size parameter, so it can't recurse. For compound cases like `seq_left (h : HasThrowInHead a)` with expr `.seq a b`, you need to:
1. Show that normalizeExpr (.seq a b) k produces .throw arg
2. Decompose: normalizeExpr first normalizes a with a continuation that wraps b
3. The throw must come from normalizing a (since b's continuation can't produce throw)
4. Apply the IH on a (smaller expression)
5. Lift the flat steps through the seq eval context using `Steps_seq_ctx` (L2446)

### THE FIX: ADD DEPTH INDUCTION
Refactor `normalizeExpr_throw_step_sim` to take a depth parameter `d : Nat` with `hd : sf.expr.depth ≤ d`:

```lean
private theorem normalizeExpr_throw_step_sim
    (d : Nat)
    (sf : Flat.State)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.throw arg, m))
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (hewf : ExprWellFormed sf.expr sf.env)
    (hna : NoNestedAbrupt sf.expr)
    (hd : sf.expr.depth ≤ d) :
    ...
```

Then in the compound cases, use `ih` on sub-expressions with `d' < d` via `Nat.lt_of_lt_of_le`.

**Infrastructure that already exists (USE THESE):**
- `Steps_seq_ctx` (L2446): lift steps through `.seq · b` context
- `Steps_let_ctx` (search for it): lift through `.let name · body`
- `step?_seq_ctx` (L1546): single step in seq context
- Similar `Steps_*_ctx` for getProp, setProp, binary, unary, call, newObj, etc.

### CONCRETE STEPS:
1. Use `lean_goal` at L11713 to see exact proof state
2. Replace the `| _ =>` with explicit cases for each HasThrowInHead constructor
3. For each case (e.g., `| seq_left h_a =>`):
   a. Unfold normalizeExpr for .seq
   b. Show the throw comes from normalizing the sub-expression a
   c. YOU CANNOT RECURSE (no depth param yet) — so first just enumerate the cases with individual sorries
   d. Then add the depth parameter to the theorem signature
4. Once you have depth param, prove each case by: IH on sub-expr + Steps_*_ctx to lift

**START BY**: Just case-splitting L11713 into individual cases, each with its own sorry. Going from 1 sorry to ~26 sorries is PROGRESS because each is independently attackable.

## ===== P1: REMAINING COMPOUND SORRIES (same pattern) =====

L11864, L11870, L12041, L12047, L12199, L12205 — return/await/yield variants.
Once you add depth to throw, do the same for return/await/yield.

## ===== P2: STRUCTURAL SORRIES (L12261, L12265, L12266) =====

These are in `anfConvert_step_star`. Use `lean_goal` to understand.

## ===== P3: WHILE + TRYCATCH + CALLFRAME + BREAK (8 sorries) =====

L12356, L12368, L16366, L16384, L16387, L17470, L17481, L17701, L17754

## WORKFLOW
1. Start with `lean_goal` at L11713 to see the exact proof state
2. Try `lean_multi_attempt` with candidate tactics
3. If a tactic works, edit the file to replace the sorry
4. Verify with `lean_diagnostic_messages` after editing
5. Move to next sorry

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
