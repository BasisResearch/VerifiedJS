# proof — KEEP CLOSING SECOND-POSITION CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T18:05
- ANF: 43 real sorries. CC: 12. Total: 55.
- **YOU CLOSED binary_rhs!** Great work. The proof at L17090-17133 is the template for all remaining cases.
- 4 second-position + 2 call/newObj = 6 more to close using the EXACT same pattern.

## YOUR TARGET: L17134-L17137 (4 second-position sorries)

### VERIFIED LINE NUMBERS (from file at 18:05):
```
L17134: | setProp_val h_a => sorry
L17135: | getIndex_idx h_a => sorry
L17136: | setIndex_idx h_a => sorry
L17137: | setIndex_val h_a => sorry
```

### YOUR TEMPLATE: binary_rhs proof at L17090-17133
You JUST wrote this. Each of the 4 remaining cases follows the EXACT same structure. Just substitute:

| Case | Wrapper | ctx lemma | error lemma |
|------|---------|-----------|-------------|
| setProp_val | `(.setProp (.lit ov) prop ·)` | step?_setProp_val_ctx | step?_setProp_val_error |
| getIndex_idx | `(.getIndex (.lit ov) ·)` | step?_getIndex_idx_ctx | step?_getIndex_idx_error |
| setIndex_idx | `(.setIndex (.lit ov) · val)` | step?_setIndex_idx_ctx | step?_setIndex_idx_error |
| setIndex_val | `(.setIndex (.lit ov) (.lit iv) ·)` | step?_setIndex_val_ctx | step?_setIndex_val_error |

### APPROACH: Copy-paste binary_rhs, change lemma names
1. Read L17090-17133 (your binary_rhs proof)
2. Copy structure for setProp_val at L17134. Replace ctx/error lemma names. Verify.
3. Repeat for getIndex_idx, setIndex_idx, setIndex_val.
4. Each case should take ~5 min since you already have the working pattern.

## AFTER P0: call_env, newObj_env (L17138, L17140)
Same pattern. Lemmas:
- `step?_call_env_ctx` / `step?_call_env_error`
- `step?_newObj_env_ctx` / `step?_newObj_env_error`

## DO NOT WORK ON:
- L10796-L11167 (trivialChain — LSP timeout zone)
- L17824-L17836 (while — blocked)
- L18561-L18601 (if_branch — blocked)
- L19442-L19463 (tryCatch — blocked)
- L20790-L20801 (noCallFrameReturn/body_sim — blocked)
- ClosureConvertCorrect.lean

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — remaining second-position L17134-L17137" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
