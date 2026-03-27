# jsspec — Prepare CC expression patches + analyze call/newObj cases

## STATUS: You CANNOT write to ClosureConvertCorrect.lean (owned by proof agent)
Your patches in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_expr_patches.lean` for setProp/setIndex are ready.
The proof agent has been instructed to install them.

## YOUR TASK: Analyze and document remaining expression cases

### Priority 1: call (L2524) and newObj (L2525)

These are full sorry expressions. Analyze the goal and write complete proof patches:

1. Read ClosureConvertCorrect.lean L2524-2525 context
2. Use `lean_goal` to check what the exact goal is at those lines
3. Read how `Flat.convertExpr` handles `.call f args`:
   - It converts f and each arg, producing a flat call
   - The stepping logic: if f is not a value, step f; else if some arg is not a value, step that arg; else execute the call
4. Check if helper lemmas `Flat_step?_call_*` and `Core_step?_call_*` exist
5. Write the proof patch to `.lake/_tmp_fix/VerifiedJS/Proofs/cc_call_patches.lean`

### Priority 2: objectLit (L2795), arrayLit (L2796), functionDef (L2797)

1. **functionDef**: This should be simple — `functionDef` is a value in Core, so `Core.exprValue?` returns `some`. The Flat side converts to a closure allocation. Check if `Flat.step?` on the converted form returns `none` (contradiction with hstep) or if it allocates.

2. **objectLit/arrayLit**: These involve list-based conversion (`convertExprList`/`convertPropList`). Check the Flat stepping for these — do they step the first non-value element?

3. Write patches to `.lake/_tmp_fix/VerifiedJS/Proofs/cc_expr2_patches.lean`

### Priority 3: tryCatch (L2887)

Read the tryCatch conversion and stepping. This is complex (error propagation). Document:
- What `Flat.convertExpr (.tryCatch body catchParam catchBody finally_)` produces
- What `Flat.step?` does on the converted form
- What `Core.step?` does on `.tryCatch`
- Write a skeleton proof or identify which sub-cases are easy vs hard

## PATCH FORMAT

For each patch, write:
```lean
-- PATCH for L<line>: <case name>
-- Replace: sorry
-- With:
<exact proof text>
```

Include all needed helper lemmas with their full statements and proofs.

## What NOT to do:
- Do NOT try to edit ClosureConvertCorrect.lean (you don't have write access)
- Do NOT touch ANF, Wasm, or Lower files
- Do NOT start a lake build of the full project

## Build (for checking helpers): `lake build VerifiedJS.Core.Semantics`
## Log progress to agents/jsspec/log.md.
