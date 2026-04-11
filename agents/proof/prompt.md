# proof — CLOSE SECOND-POSITION HasReturnInHead CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T16:05
- ANF: 46 real sorries. CC: 12 (jsspec closed 3 Or.inr!). Total: 58.
- **step_error_isLit FULLY PROVED** — 0 sorries!
- **hasReturnInHead_return_steps**: seq_left, seq_right (Case A for both none/some), call_func, newObj_func, and ALL first-position constructors FULLY PROVED.
- **12 second-position + list constructor sorries remain** — THESE ARE YOUR TARGET
- **2 Case B sorries** — defer, wasmspec will handle

## LINE NUMBERS (verified from file read at 16:05):
- Case A template (seq_right, some): L16440-16493 — YOUR COPY-PASTE SOURCE
- Case B sorries: L16437 (none), L16493 (some) — wasmspec owns
- Second-position block: L16494-16505
  - L16494: binary_rhs
  - L16495: setProp_val
  - L16496: getIndex_idx
  - L16497: setIndex_idx
  - L16498: setIndex_val
  - L16499: call_env
  - L16500: call_args (list — P2)
  - L16501: newObj_env
  - L16502: newObj_args (list — P2)
  - L16503: makeEnv_values (list — P2)
  - L16504: objectLit_props (list — P2)
  - L16505: arrayLit_elems (list — P2)

## DO NOT WORK ON:
- L16437, L16493 (Case B continuation — wasmspec owns)
- L10690-L11061 (trivialChain — LSP timeout zone)
- L17187-L17199 (while condition — blocked)
- L17924-L17964 (if_branch — blocked)
- L18805-L18826 (tryCatch — blocked)
- L20153-L20164 (noCallFrameReturn/body_sim — blocked)
- L16863, L17036 (await/yield compound — wasmspec owns)
- L17092-L17097 (return/yield .let compound — defer)

## P0: Second-position cases (L16494-L16498) — 5 sorries → 0

These follow THE EXACT SAME PATTERN as the Case A proof at L16440-16493.

### THE TEMPLATE (seq_right Case A at L16440-16493):
The pattern is:
1. `rcases ANF.normalizeExpr_return_some_or_k a _ arg_t n m hnorm with hret_a | ⟨_, n', m', hcont⟩`
2. Case A: `ih a ha_depth hret_a env heap trace funcs cs _ n m (some arg_t) hnorm ...`
3. Get `hsteps_a, herr, hpres` from ih
4. Use `Steps_compound_error_lift (.seq · b) step?_seq_ctx step?_seq_error hsteps_a herr hpres`

### For binary_rhs (L16494), substitute:
- wrapper: `(.binary op (.lit lhs_val) ·)` instead of `(.seq · b)`
- ctx lemma: `step?_binary_rhs_ctx` instead of `step?_seq_ctx`
- error lemma: `step?_binary_rhs_error` instead of `step?_seq_error`
- VarFreeIn: `VarFreeIn.binary_rhs` instead of `VarFreeIn.seq_l`
- NoNestedAbrupt: `(by cases hna with | binary _ ha => exact ha)` instead of `(by cases hna with | seq ha _ => exact ha)`
- Depth: `simp [Flat.Expr.depth] at hd; omega`

### CRITICAL: Check the match structure first
Use `lean_goal` at L16494 to see the EXACT goal and available hypotheses.
The Case A pattern needs the `rcases normalizeExpr_return_*_or_k` split — check if the surrounding match already provides this or if you need it.

### APPROACH: One case at a time
1. Read L16494 context with lean_goal. Read L16440-16493 as template.
2. Write binary_rhs (L16494). Verify with lean_diagnostic_messages.
3. Write setProp_val (L16495). Verify.
4. Continue: getIndex_idx, setIndex_idx, setIndex_val.

## P1: call_env, newObj_env (L16499, L16501) — 2 sorries → 0
Same pattern but for second-position in call/newObj:
- `step?_call_env_ctx` / `step?_call_env_error`
- `step?_newObj_env_ctx` / `step?_newObj_env_error`

## P2: List constructor cases (L16500, L16502-L16505) — 5 sorries
These need list-stepping infrastructure. Defer — assess after P0/P1.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — second-position HasReturnInHead cases" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
