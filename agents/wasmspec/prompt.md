# wasmspec — if_branch list cases in ANFConvertCorrect.lean

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~3.5GB free. USE LSP ONLY — no builds.

## STATUS: Rate limits blocked all agents for 18 hours. Fresh start.

## CONCURRENCY
- proof agent works on L11550-12400 (throw/return/await/yield) and L16366-17754 (tryCatch/callframe/break)
- jsspec works on ClosureConvertCorrect.lean
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

### FALSE branch (L15210-15525): same pattern as true branch

### Classification:
- **7 second-position** per branch (14 total): CONFIRMED UNFIXABLE without theorem redesign. Skip these.
- **5 list cases** per branch (10 total): YOUR PRIORITY

## ===== FOCUS: LIST CASES (10 sorries) =====

True branch list cases: L14026, L14099, L14228, L14260, L14291
False branch list cases: L15260, L15333, L15462, L15494, L15525

### Approach:
1. `lean_goal` at L14026 to see the exact proof state for call_args
2. The if is inside a list element (args), not the function/head. Pattern:
   - f and env don't have HasIfInHead
   - One element in args has HasIfInHead
   - Need to step through f/env evaluation, then into the list
3. Consider writing a helper lemma `normalizeExprList_if_branch_step` for list induction
4. Use `lean_multi_attempt` to test tactics before editing

### Key insight: f/env are NOT the expressions with `if` in head
The sorry comment says "f has no if". The `HasIfInHead` is in the argument list. You need to:
1. Show f/env evaluate to values (they don't have if in head)
2. Show the list stepping reaches the element with HasIfInHead
3. Apply the depth induction hypothesis on that element

## WORKFLOW
1. `lean_goal` at each sorry to understand the exact state
2. `lean_multi_attempt` to test tactics
3. Edit to replace sorry
4. `lean_diagnostic_messages` to verify
5. Move to next sorry. Do all 5 true-branch list cases, then do false branch by copy.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
