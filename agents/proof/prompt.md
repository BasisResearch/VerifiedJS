# proof — 14 sorries in your zone. Line numbers UPDATED 21:05.

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.6GB available. VERY TIGHT.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count = 0.
**Do NOT start builds when wasmspec or jsspec are building. Use LSP tools instead.**

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L12000-12750 (trivialChain zone — 4 left)
- **YOU** own everything else
- DO NOT touch lines 12000-12750

## PROGRESS: Sorry count 37 total (25 ANF + 12 CC). You have 14 in your zone.

## YOUR 14 SORRIES — CURRENT LINE NUMBERS (verified 21:05)

### GROUP A-remnant: normalizeExpr_labeled_branch_step (2 sorries)
| L8754 | unary_arg: needs Steps_unary_ctx_b |
| L8755 | remaining catch-all: seq_right, setProp, binary_rhs, call, newObj, getIndex, setIndex, makeEnv, objectLit, arrayLit |

**L8754**: needs `Steps_unary_ctx_b` helper. jsspec may be building this — check if it exists yet.
**L8755**: needs more eval context helpers (`Steps_X_ctx_b` for each sub-constructor). Build them one at a time.

### GROUP B: compound HasXInHead catch-all (4 sorries)
| L10002 | compound HasThrowInHead (seq_l, let_init, if_cond, call_callee, etc.) |
| L10159 | compound HasReturnInHead |
| L10336 | compound HasAwaitInHead |
| L10494 | compound HasYieldInHead |

These need eval context stepping: for each HasXInHead sub-constructor, one Flat step through the eval context, then IH.

### GROUP C: compound inner_val/inner_arg (3 sorries)
| L10153 | throw compound inner_val (non-trivial cases like seq, let, etc.) |
| L10330 | return compound inner_arg |
| L10488 | yield compound inner_val |

### GROUP D: return/yield/compound (3 sorries)
| L10550 | return (some val): compound, can produce .let |
| L10554 | yield (some val): compound, can produce .let |
| L10555 | compound expressions catch-all |

### GROUP E: while (2 sorries)
| L10645 | While condition value case |
| L10657 | Condition-steps case |

### GROUP F: tryCatch/call/break (7 sorries) — BLOCKED, do NOT work on these
| L13578, L13596, L13599, L14682, L14693, L14913, L14966 |

## PRIORITY ORDER
1. **GROUP B** (4 compound HasXInHead) — highest-value targets. Each one eliminates 1 sorry by case-splitting on HasXInHead constructors and stepping through eval context.
2. **GROUP C** (3 inner_val/arg) — similar pattern to Group B
3. **L8754 + L8755** — needs Steps_X_ctx_b helpers (check if jsspec built any)
4. **GROUP D/E** — later

## STRATEGY FOR GROUP B (HasXInHead)
For L10002 (HasThrowInHead), the sorry says "compound HasThrowInHead cases: need eval context stepping through seq/let/call/etc."

Use `lean_goal` at L10002 to see the goal. The pattern is:
1. `hthrow : HasThrowInHead e` — gives you the sub-constructor (seq_l, let_init, etc.)
2. Match on `hthrow` — each case gives an eval context position
3. For each case, apply IH to the inner expression, then lift through the eval context using existing `Steps_X_ctx_b`

This is the SAME pattern you used successfully for Group A. Repeat it.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
