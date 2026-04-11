# proof — CLOSE LIST CASES (5 sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T20:05
- ANF: 37 real sorries. CC: 12. Total: **49**.
- **Great work closing call_env + newObj_env!** Second-position cases are DONE.
- Next: 5 list cases in HasReturnInHead_anfConvert_step_sim.

## YOUR TARGET: List cases (5 sorries)

### VERIFIED LINE NUMBERS:
```
L18952: | call_args h_a => sorry -- list: return in args of call f env args
L19261: | newObj_args h_a => sorry -- list: return in args of newObj f env args
L19262: | makeEnv_values h_a => sorry -- list: return in values of makeEnv values
L19263: | objectLit_props h_a => sorry -- list: return in props of objectLit props
L19264: | arrayLit_elems h_a => sorry -- list: return in elems of arrayLit elems
```

### KEY DIFFERENCE FROM SECOND-POSITION: these operate on LISTS
- `h_a : HasReturnInHeadList args` (or HasReturnInHeadProps for objectLit)
- The args list has one element with HasReturnInHead
- Flat.step? evaluates the FIRST non-value element in the list
- Need to show: the first non-value element IS the one with HasReturnInHead

### STRATEGY for call_args (L18952):
1. Use `lean_hover_info` on `HasReturnInHeadList` to understand its structure
2. You need a lemma like: `HasReturnInHeadList args → ∃ i e, args[i] = e ∧ HasReturnInHead e ∧ (∀ j < i, isValue args[j])`
   - OR induction on HasReturnInHeadList to find the first non-value element
3. The wrapper is `(.call (.lit fv) (.lit ev) ·)` (both f and env are values)
4. ctx lemma: `step?_call_args_ctx` (search with lean_local_search)
5. error lemma: `step?_call_args_error` (search with lean_local_search)
6. IH applies to the element with HasReturnInHead

### APPROACH:
1. **First**: Check what helpers exist. Use `lean_local_search "HasReturnInHeadList"` and `lean_local_search "firstNonValue"` and `lean_local_search "call_args"`.
2. **Check line numbers**: Use `lean_hover_info` at L18952 to confirm the sorry is still there.
3. **Try call_args first** (L18952). If the list infrastructure is missing, you may need to write a helper lemma first.
4. If call_args works, the other 4 follow the same pattern.

### FALLBACK: If list cases are too complex
Switch to break/continue list cases (L4906, L6044) which are simpler 3-constructor matches.

## DO NOT WORK ON:
- L10843-L11214 (trivialChain — LSP timeout zone)
- L19620, L19793 (await/yield compound — blocked)
- L19849-L19854 (return/yield .let compound — blocked)
- L19944-L19956 (while — blocked)
- L20681-L20721 (if_branch — blocked)
- L21562-L21583 (tryCatch — blocked)
- L22910-L23211 (end-of-file — blocked)
- ClosureConvertCorrect.lean

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — list cases L18952+L19261-L19264" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
