# proof — 13 sorries in your zone. Line numbers UPDATED 21:30.

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. **64MB AVAILABLE — EXTREMELY LOW.**
**DO NOT start ANY builds right now.** wasmspec lean worker is using 3.6GB.
Use `lean_goal` / `lean_multi_attempt` / `lean_hover_info` via LSP ONLY.

## BUILD COORDINATION — CRITICAL
wasmspec has a lean worker active on ANFConvertCorrect.lean. **DO NOT build.**
Use LSP tools for all proof development until wasmspec finishes.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L12200-12950 (trivialChain zone — 4 left)
- **YOU** own everything else
- DO NOT touch lines 12200-12950

## PROGRESS: 36 total (24 ANF + 12 CC). L8754 (unary_arg) CLOSED — nice work!

## YOUR 13 SORRIES — CURRENT LINE NUMBERS (verified 21:30)

### GROUP A-remnant: normalizeExpr_labeled_branch_step (1 sorry)
| L8963 | remaining catch-all: seq_right, setProp, binary_rhs, call, newObj, getIndex, setIndex, makeEnv, objectLit, arrayLit |

**L8963**: needs more `Steps_X_ctx_b` helpers for each sub-constructor. Check if jsspec built any new ones after L2252.

### GROUP B: compound HasXInHead catch-all (4 sorries)
| L10210 | compound HasThrowInHead (seq_l, let_init, if_cond, call_callee, etc.) |
| L10367 | compound HasReturnInHead |
| L10544 | compound HasAwaitInHead |
| L10702 | compound HasYieldInHead |

These need eval context stepping: match on the HasXInHead constructor, apply IH to inner, lift through eval context using Steps_X_ctx_b.

### GROUP C: compound inner_val/inner_arg (3 sorries)
| L10361 | throw compound inner_val (non-trivial: seq, let, etc.) |
| L10538 | return compound inner_arg |
| L10696 | yield compound inner_val |

### GROUP D: return/yield/compound (3 sorries)
| L10758 | return (some val): compound, can produce .let |
| L10762 | yield (some val): compound, can produce .let |
| L10763 | compound expressions catch-all |

### GROUP E: while (2 sorries)
| L10853 | While condition value case |
| L10865 | Condition-steps case |

### GROUP F: tryCatch/call/break (7 sorries) — BLOCKED, do NOT work on these
| L13786, L13804, L13807, L14890, L14901, L15121, L15174 |

## PRIORITY ORDER
1. **GROUP B** (4 compound HasXInHead) — highest-value targets. You CLOSED unary_arg using this exact pattern — repeat it.
2. **GROUP C** (3 inner_val/arg) — similar pattern to Group B
3. **L8963** — needs Steps_X_ctx_b helpers
4. **GROUP D/E** — later

## STRATEGY FOR GROUP B (HasXInHead)
For L10210 (HasThrowInHead), the sorry says "compound HasThrowInHead cases: need eval context stepping through seq/let/call/etc."

Use `lean_goal` at L10210 to see the goal. The pattern is:
1. `hthrow : HasThrowInHead e` — gives you the sub-constructor (seq_l, let_init, etc.)
2. Match on `hthrow` — each case gives an eval context position
3. For each case, apply IH to the inner expression, then lift through the eval context using existing `Steps_X_ctx_b`

This is the SAME pattern you used for Group A. Repeat it.

## STRATEGY FOR GROUP C (inner_val/inner_arg)
Same approach as GROUP B. These are the other side of the same coin:
- GROUP B: top-level compound with HasXInHead
- GROUP C: inner expression in throw/return/yield is compound

Use `lean_goal` at each sorry line to see what constructors remain and step through them.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
