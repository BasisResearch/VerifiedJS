# jsspec — Close CC expression-level sorries (setProp, setIndex, objectLit, arrayLit, functionDef, tryCatch)

## STATUS: convertExpr_state_determined is COMPLETE ✓

## YOUR TASK: Close expression-level CC sorries

The proof agent is doing the suffices CCStateAgree refactor (see proof/prompt.md for details).
YOU should work on the expression cases that are full sorry (not CCState-related).

### Target sorries in ClosureConvertCorrect.lean:

1. **L2583: setProp** — `| setProp obj prop value => sorry`
   - Read L2560-2600 for context
   - Pattern: unfold convertExpr for setProp, show the obj sub-expression steps similarly to getProp/binary
   - Use helper lemmas `Flat_step?_setProp_obj_step` and `Core_step?_setProp_obj_step` if they exist
   - `lean_goal` at L2583 to see the goal

2. **L2646: setIndex** — `| setIndex obj idx value => sorry`
   - Similar to setProp but with index

3. **L2794: objectLit** — `| objectLit props => sorry`
   - Read L2780-2810 for context
   - May need list-based conversion reasoning

4. **L2795: arrayLit** — `| arrayLit elems => sorry`
   - Similar to objectLit

5. **L2796: functionDef** — `| functionDef fname params body isAsync isGen => sorry`
   - This is a VALUE in Core (functionDef evaluates to itself/closure)
   - So `Flat.step?` on the converted form should be `none` → contradiction with `hstep`
   - Check if `convertExpr (.functionDef ...)` produces a value (like `.lit`)

6. **L2886: tryCatch** — `| tryCatch body catchParam catchBody finally_ => sorry`
   - Read L2870-2900 for context

### Approach for each:
1. `lean_goal` at the sorry line to see the exact goal state
2. Read surrounding proven cases (getProp at L2525, binary at L2460) as templates
3. Try `lean_multi_attempt` with candidate tactics
4. If complex, decompose with `constructor`/`refine`

### IMPORTANT: The suffices is being refactored by proof agent
The proof agent may change the structure of the suffices (moving scope/st/st' from existential to universal, adding CCStateAgree). If you see new type errors in the expression cases after the proof agent's changes, adapt:
- The input `hconv` will change from `⟨scope, st, st', hconv⟩` to direct `hconv`
- The output needs `⟨st_a, st_a', hconv_new, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩` for non-stepping cases

### What NOT to do:
- Do NOT touch CCState sorries (L1987, L2194, L2283, L2522, L2645, L2917) — proof agent owns those
- Do NOT touch the suffices statement — proof agent is refactoring it
- Do NOT touch ANF, Wasm, or Lower files
- Do NOT break the build

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log progress to agents/jsspec/log.md.
