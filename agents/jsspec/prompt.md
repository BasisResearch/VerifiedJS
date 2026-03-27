# jsspec — convertExpr_state_determined is DONE. Help close CC expression cases.

## STATUS: convertExpr_state_determined is COMPLETE ✓ (no sorry). All stepping lemmas DONE ✓.

## NEW TASK: Help close CC expression-level sorries

The proof agent is working on CCState sorries (P1). You should work on the non-CCState expression cases.

### Target sorries in ClosureConvertCorrect.lean:

1. **L2573: setProp** — `| setProp obj prop value => sorry`
   - Read context around L2560-2580
   - This needs to show that `setProp` conversion produces a matching Flat expression
   - Use `lean_goal` at L2573 to see what's needed
   - Pattern: unfold convertExpr, show the Flat step matches the Core step

2. **L2632: setIndex** — `| setIndex obj idx value => sorry`
   - Similar to setProp but with index instead of property
   - Read context around L2620-2650

3. **L2784: objectLit** — `| objectLit props => sorry`
   - Read context around L2780-2800
   - May need `convertExprList` lemma for property list

4. **L2785: arrayLit** — `| arrayLit elems => sorry`
   - Similar to objectLit

5. **L2786: functionDef** — `| functionDef fname params body isAsync isGen => sorry`
   - This involves closure creation via `addFunc`/`freshVar`
   - Key: the Flat version uses `makeClosure` with the func index from CCState

6. **L2876: tryCatch** — `| tryCatch body catchParam catchBody finally_ => sorry`
   - Read context around L2870-2880

### Approach for each:
1. `lean_goal` at the sorry line
2. `lean_multi_attempt` with candidate tactics
3. If the goal is complex, decompose into smaller sub-goals with `constructor` or `refine`

### What NOT to do:
- Do NOT touch CCState sorries (L1973, L2180, L2269, L2508, L2631, L2903) — proof agent owns those
- Do NOT touch ANF, Wasm, or Lower files
- Do NOT break the build

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log progress to agents/jsspec/log.md.
