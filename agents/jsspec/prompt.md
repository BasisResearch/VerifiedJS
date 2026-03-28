# jsspec — ANF HELPER LEMMAS (CRITICAL PATH)

## STATUS: 59 sorries. Your CCStateAgree helpers are excellent. NOW: proof agent is pivoting to ANF. It needs helpers.

## PRIORITY 0: Write ANF step? simp lemmas

File: `.lake/_tmp_fix/VerifiedJS/Proofs/anf_helpers.lean`

The proof agent needs simp lemmas for each ANF constructor. Use `lean_hover_info` on `ANF.step?` and `Source.step?` to understand the definitions, then write:

1. **break/continue**: What does `ANF.step? (.break label) env heap` reduce to? Write the simp lemma.
2. **throw**: `ANF.step? (.throw arg) env heap` — evaluate trivial arg, produce throw event.
3. **return**: `ANF.step? (.return arg) env heap` — similar.
4. **var lookup**: `ANF.step? (.var name) env heap` — resolve in env.

Also write **normalizeExpr inversion lemmas**:
5. What does `normalizeExpr (.break label) k` produce?
6. What does `normalizeExpr (.throw e) k` produce?
7. What does `normalizeExpr (.return e) k` produce?

Use `lean_hover_info` on `normalizeExpr` to understand the definition.

Verify each with `lake env lean` on the staging file.

## PRIORITY 1: Install CC patches into main file

The proof agent may not have installed your staged helpers yet. If you can write to CC file, install:
1. CCStateAgree helpers from `cc_agree_helpers.lean` (ABOVE the main theorem)
2. The `@[simp]` lemmas from `cc_st_lemma.lean`
3. The L2138 fix: replace 2nd `sorry` with `⟨rfl, rfl⟩`

## PRIORITY 2: Prepare call/newObj patches for proof agent

Update the cc_call_patches.lean with current line numbers if they've shifted.

## What NOT to do:
- Do NOT run full `lake build`
- Do NOT edit Wasm/Semantics.lean

## Log progress to agents/jsspec/log.md.
