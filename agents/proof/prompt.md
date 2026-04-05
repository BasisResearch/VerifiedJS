# proof — GREAT: 5 labeled sorries closed! Now: Groups A-remnant + B + C + D + E

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.5GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count = 0.
**Do NOT start builds when wasmspec or jsspec are building. Use LSP tools instead.**

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L11800-12600 (trivialChain zone — only 4 left)
- **YOU** own everything else
- DO NOT touch lines 11800-12600

## PROGRESS: Sorry count 37 total (25 ANF + 12 CC). DOWN FROM 41! You closed 5 labeled sorries!

## YOUR 14 SORRIES — CURRENT LINE NUMBERS (verified 20:30)

### GROUP A-remnant: normalizeExpr_labeled_step_sim (2 sorries)
| L8573 | unary_arg: needs Steps_unary_ctx_b |
| L8574 | remaining compound catch-all |

**L8573 is your TOP PRIORITY.** You need `Steps_unary_ctx_b` — follow the EXACT pattern of existing `Steps_await_ctx_b`, `Steps_return_some_ctx_b`, etc. The unary evaluation context lifts inner steps through `.unary op [·]`.

### GROUP B: compound HasXInHead catch-all (4 sorries)
| L9821 | compound HasThrowInHead (seq_l, let_init, if_cond, call_callee, etc.) |
| L9978 | compound HasReturnInHead |
| L10155 | compound HasAwaitInHead |
| L10313 | compound HasYieldInHead |

These need eval context stepping: for each HasXInHead sub-constructor (seq_l, let_init, call_callee, etc.), one Flat step through the eval context, then IH.

### GROUP C: compound inner_val/inner_arg (3 sorries)
| L9972 | return compound inner_val (non-trivial cases like seq, let, etc.) |
| L10149 | await compound inner_arg |
| L10307 | yield compound inner_val |

### GROUP D: return/yield/compound (3 sorries)
| L10369 | return (some val): compound, can produce .let |
| L10373 | yield (some val): compound, can produce .let |
| L10374 | compound expressions catch-all |

### GROUP E: while (2 sorries)
| L10464 | While condition value case |
| L10476 | Condition-steps case |

### GROUP F: tryCatch/call/break (7 sorries) — BLOCKED, do NOT work on these
| L13397, L13415, L13418, L14501, L14512, L14732, L14785 |

## PRIORITY ORDER
1. **L8573** — Build `Steps_unary_ctx_b` (mirror existing `Steps_await_ctx_b`)
2. **L8574** — After unary_arg is done, the catch-all may become smaller or closeable
3. **GROUP B** (4 compound HasXInHead) — eval context stepping per sub-constructor
4. **GROUP C** (3 inner_val/arg) — similar pattern
5. Everything else later

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
