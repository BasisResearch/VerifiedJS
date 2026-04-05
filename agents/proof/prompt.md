# proof — Keep pushing! 1 more labeled sorry closed. Now: 13 sorries in your zone.

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
- wasmspec works on L12100-12900 (trivialChain zone — 4 left)
- **YOU** own everything else
- DO NOT touch lines 12100-12900

## PROGRESS: Sorry count 36 total (24 ANF + 12 CC). DOWN FROM 37! You have 13 in your zone.

## YOUR 13 SORRIES — CURRENT LINE NUMBERS (verified 21:00)

### GROUP A-remnant: normalizeExpr_labeled_branch_step (1 sorry)
| L8915 | remaining catch-all: seq_right, setProp, binary_rhs, call, newObj, getIndex, setIndex, makeEnv, objectLit, arrayLit |

**L8915 needs more eval context helpers.** Each sub-constructor needs its own `Steps_X_ctx_b` (like Steps_binary_rhs_ctx_b, Steps_call_func_ctx_b, etc.). Build them one at a time following the pattern of existing helpers.

### GROUP B: compound HasXInHead catch-all (4 sorries)
| L10162 | compound HasThrowInHead (seq_l, let_init, if_cond, call_callee, etc.) |
| L10319 | compound HasReturnInHead |
| L10496 | compound HasAwaitInHead |
| L10654 | compound HasYieldInHead |

These need eval context stepping: for each HasXInHead sub-constructor, one Flat step through the eval context, then IH.

### GROUP C: compound inner_val/inner_arg (3 sorries)
| L10313 | throw compound inner_val (non-trivial cases like seq, let, etc.) |
| L10490 | return compound inner_arg |
| L10648 | yield compound inner_val |

### GROUP D: return/yield/compound (3 sorries)
| L10710 | return (some val): compound, can produce .let |
| L10714 | yield (some val): compound, can produce .let |
| L10715 | compound expressions catch-all |

### GROUP E: while (2 sorries)
| L10805 | While condition value case |
| L10817 | Condition-steps case |

### GROUP F: tryCatch/call/break (7 sorries) — BLOCKED, do NOT work on these
| L13738, L13756, L13759, L14842, L14853, L15073, L15126 |

## PRIORITY ORDER
1. **GROUP B** (4 compound HasXInHead) — these are the highest-value targets. Each one eliminates 1 sorry by case-splitting on HasXInHead constructors and stepping through eval context.
2. **GROUP C** (3 inner_val/arg) — similar pattern to Group B
3. **L8915** — needs more Steps_X_ctx_b helpers (binary_rhs, call_func, etc.)
4. **GROUP D/E** — later

## STRATEGY FOR GROUP B (HasXInHead)
For L10162 (HasThrowInHead), the sorry says "compound HasThrowInHead cases: need eval context stepping through seq/let/call/etc."

Use `lean_goal` at L10162 to see the goal. The pattern is:
1. `hthrow : HasThrowInHead e` — gives you the sub-constructor (seq_l, let_init, etc.)
2. Match on `hthrow` — each case gives an eval context position
3. For each case, apply IH to the inner expression, then lift through the eval context using existing `Steps_X_ctx_b`

This is the SAME pattern you used successfully for Group A. Repeat it.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
