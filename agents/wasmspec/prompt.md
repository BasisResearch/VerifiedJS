# wasmspec — if_branch second-position + list cases

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~1.5GB free. USE LSP ONLY — no builds. DO NOT launch lean_build.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11568+ (throw/return/await/yield step_sim refactoring), L12292+ (seq/while), L16349+ (tryCatch), L17296+ (anfConvert_step_star)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own L13034-15612 ONLY (if_branch_step and if_branch_step_false)

## ===== K-MISMATCH STATUS: CONFIRMED UNFIXABLE =====

The 14 second-position sorry cases (7 per theorem) at L13959, L13984, L14106, L14130, L14155, L14180 (true) and corresponding false cases CANNOT be proved without theorem redesign. The `body` parameter is load-bearing.

**Do not spend more time on second-position cases.**

## ===== YOUR PRIORITY: LIST CASES (10 sorries, 5 per theorem) =====

These are the list-based HasIfInHead constructors in if_branch_step:
```
TRUE branch:
L14009: · sorry -- f has no if: requires stepping f/env to values + list decomposition  (call_args)
L14057: · sorry  (newObj_args)
L14082: · sorry -- f has no if: requires stepping f/env to values + list decomposition  (makeEnv_values)
L14211: · sorry -- first element has no if: requires stepping + list recursion  (objectLit_props)
L14243: · sorry -- first prop value has no if: requires stepping + list recursion  (arrayLit_elems)

FALSE branch:
L15243: · sorry -- f has no if  (call_args)
L15291: · sorry  (newObj_args)
L15316: · sorry -- f has no if  (makeEnv_values)
L15445: · sorry -- first element has no if  (objectLit_props)
L15477: · sorry -- first prop value has no if  (arrayLit_elems)
```

### Approach for list cases:
These are cases where `HasIfInHead` is in a list element (args, props, etc.) but NOT in the function/head expression. Pattern:

1. `call_args`: `HasIfInHead` is in one of `args`. The function `f` does NOT have if in head.
   - The if is inside an argument. Use `Classical.em (HasIfInHead f)`:
     - If f has if: use ih on f (already proved above)
     - If f doesn't have if: f must be value or trivial chain. Step f to value, then step args.
   - **Key**: after f/env are values, we're stepping within the argument list. Need list induction on args to find the element with HasIfInHead.
   - May need a helper lemma: `normalizeExprList_if_branch_step` that does induction on the list.

2. Similar for `newObj_args`, `makeEnv_values`, `objectLit_props`, `arrayLit_elems`.

### Potential helper lemma:
```lean
private theorem normalizeExprList_if_branch_step :
    ∀ (d : Nat) (es : List Flat.Expr), (∀ e ∈ es, e.depth ≤ d) →
    HasIfInHeadList es →
    ... →
    ∃ (sf' : ...) (evs : ...),
      -- steps through list evaluation context to reduce the if-containing element
```

Use `lean_goal` on L14009 to see the exact proof state, then build from there.

## P1: RESEARCH — K-mismatch resolution (write to agents/wasmspec/k_mismatch_analysis.md)

Only if you finish list cases. Investigate whether `ANF_SimRel` (around L114-121) can be weakened.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
