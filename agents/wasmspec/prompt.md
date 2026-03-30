# wasmspec — Close CC value sub-cases + functionDef + tryCatch

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell)
- **NEVER** use a `while` loop waiting for processes. Single `pgrep -x lake` check then proceed.
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## STATE (22:05): CC has 15 real sorries (after jsspec deletes 22 dead-code)

## YOUR TARGETS (4 value sub-cases + 2 large theorems):

### TARGET 1: Value sub-cases — HIGHEST PRIORITY

These are ALL the same pattern: all sub-expressions are values, so both Core and Flat
take one matching step (allocation, property access, etc.).

**L3692**: `| some cv => sorry -- callee is value: arg stepping or call execution`
**L4433**: `| some cv => sorry -- value sub-case (heap reasoning needed)`
**L4755**: `sorry -- all props are values: heap allocation`
**L4938**: `sorry -- all elements are values: heap allocation`

APPROACH for each:
1. `lean_goal` at the sorry line → read FULL goal
2. `lean_local_search "allValues"` and `lean_local_search "value_step"` for helpers
3. When all sub-exprs are values, Core.step? and Flat.step? should BOTH take exactly
   one step. The proof is: construct the matching steps, show results correspond.
4. `lean_multi_attempt` with:
   ```
   ["simp_all", "exact ⟨_, _, rfl, rfl⟩", "constructor <;> simp_all",
    "refine ⟨_, _, ?_, ?_⟩ <;> simp_all", "aesop"]
   ```
5. If the goal has `∃ sf' evs, Flat.Steps ...`, build the witness explicitly:
   `exact ⟨{sf with expr := ..., heap := ...}, [ev], .tail ⟨by unfold Flat.step?; simp⟩ (.refl _), ...⟩`

### TARGET 2: functionDef (L5116)
`| functionDef fname params body isAsync isGen => sorry`

functionDef creates a closure and binds fname in env. Both Core and Flat should
produce equivalent bindings. `lean_goal` → look for closure value correspondence.

### TARGET 3: tryCatch (L5206)
`| tryCatch body catchParam catchBody finally_ => sorry`

Sets up exception handler context. Core enters try body; Flat enters converted body
with catch frame pushed.

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf stubs (L1502-1503) — unprovable
- "Fix D reverted" sorries — jsspec is deleting these
- CCState threading sorries (L2857, L3176, L3198, L5237) — jsspec owns these
- convertExpr_not_lit (L2663, L2773) — jsspec owns these
- getIndex string mismatch (L4261) — possibly unprovable

## WORKFLOW:
1. `lean_goal` at the sorry line — read the FULL goal
2. `lean_multi_attempt` with 6-8 tactics
3. If nothing closes it in 10 minutes, MOVE TO THE NEXT ONE
4. Log what you tried and why it failed

## TARGET: Close at least 3 of your 6 assigned sorries
