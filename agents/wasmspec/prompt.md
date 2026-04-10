# wasmspec — if_branch list cases in ANFConvertCorrect.lean

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~3.5GB free. USE LSP ONLY — no builds.

## STATUS: ANF has 55 sorry tactics. You own 24 (12 true + 12 false branch).

## CONCURRENCY
- proof agent works on L11550-12400 and L16366-17754
- jsspec works on ClosureConvertCorrect.lean AND may help on ANF second-position cases
- **YOU** own L13976-15525 ONLY (if_branch_step true and false)

## ===== YOUR 24 SORRIES (12 true branch + 12 false branch) =====

### TRUE branch (L13976-14291):
```
L13976:  · sorry                          -- second-position (setProp_val)
L14001:  · sorry                          -- second-position (getIndex_idx)
L14026:  · sorry -- f has no if           -- list (call_args f)
L14074:  · sorry                          -- second-position (setIndex_idx)
L14099:  · sorry -- f has no if           -- list (newObj_args f)
L14123:  · sorry                          -- second-position (setIndex_val)
L14147:  · sorry                          -- second-position (call_env)
L14172:  · sorry                          -- second-position (newObj_env)
L14197:  · sorry                          -- second-position (funcE call)
L14228:  · sorry -- first element          -- list (arrayLit_elems)
L14260:  · sorry -- first prop value       -- list (objectLit_props)
L14291:  · sorry -- first element          -- list (makeEnv_values)
```

### FALSE branch (L15210-15525): mirror of true branch

### Classification:
- **7 second-position** per branch (14 total): These need K-mismatch resolution. SKIP for now.
- **5 list cases** per branch (10 total): YOUR PRIORITY

## ===== FOCUS: LIST CASES (10 sorries) =====

True branch: L14026, L14099, L14228, L14260, L14291
False branch: L15260, L15333, L15462, L15494, L15525

### Strategy for each list case:

Take L14026 (call_args — f has no if, but some arg does):

1. `lean_goal` at L14026 to see the goal. The situation:
   - Top expression is `.call f env args` with `HasIfInHead` in args (via `call_args`)
   - f does NOT have HasIfInHead
   - You need to show flat stepping reaches the arg with if-in-head

2. The proof pattern should be:
   - f and env evaluate to values (they don't have if in head, so they're trivial chains)
   - Use `Steps_call_func_ctx` to lift f's steps
   - Use `Steps_call_env_ctx` to lift env's steps
   - Then handle the list: one element has HasIfInHead
   - Use list induction to find that element, step through preceding elements
   - Apply depth IH on the element with HasIfInHead

3. Key infrastructure to search for:
   - `lean_local_search "Steps_call_arg"` — does a call_arg context lifter exist?
   - `lean_local_search "trivialChain"` — for showing f/env evaluate to values
   - `lean_local_search "HasIfInHeadList"` — list version of HasIfInHead

### If you get stuck on list induction:
Write a helper lemma first:
```lean
private theorem if_branch_step_list_helper
    (exprs : List Flat.Expr) (h : HasIfInHeadList exprs)
    ... : ...
```

### WORKFLOW for each sorry:
1. `lean_goal` at the sorry line
2. `lean_local_search` for relevant helpers
3. `lean_multi_attempt` with candidate tactics
4. If nothing works, write a helper lemma
5. Edit to replace sorry
6. `lean_diagnostic_messages` to verify
7. Do all 5 true-branch list cases first, then mirror for false branch

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
