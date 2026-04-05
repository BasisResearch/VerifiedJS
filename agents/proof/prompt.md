# proof — Close remaining ANF sorries: Group A (7 labeled) needs infrastructure FIRST

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~5GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L11053-11532 (trivialChain zone — only 4 left)
- **YOU** own everything else
- DO NOT touch lines 11053-11532

## GREAT WORK — 8 UNLOCK sorries closed last cycle!

## YOUR 22 SORRIES — CURRENT LINE NUMBERS (verified 19:05)

### GROUP A: normalizeExpr_labeled_step_sim (7 sorries) — NEEDS INFRASTRUCTURE
| L8557 | return (some non-labeled inner) — eval ctx |
| L8590 | yield (some non-labeled inner) — eval ctx |
| L8601 | return compound/bindComplex |
| L8682 | yield-return (some non-labeled inner) — eval ctx |
| L8715 | yield-yield (some non-labeled inner) — eval ctx |
| L8726 | yield compound/bindComplex |
| L8743 | overall compound/bindComplex catch-all |

**KEY INSIGHT**: These need a `normalizeExpr_labeled_or_k` lemma (analogous to the existing `normalizeExpr_tryCatch_or_k` at L8054). The pattern:
1. "If normalizeExpr e k produces .labeled, then either e has labeled in eval-head position or k produced .labeled"
2. With `hk : k produces .trivial`, k can't produce .labeled → e must have labeled in head
3. For non-labeled val in `return (some val)` or `yield (some val)`: the inner K' = `fun t => pure (.return (some t))` produces `.return`, not `.labeled`

**Strategy**: If K' can't produce .labeled AND val has no labeled in eval-head (the `| _` catch-all with val not being .labeled), then `normalizeExpr val K'` can't produce `.labeled` → exfalso.

BUT: some `| _` constructors like `.seq (.labeled ...) b` DO have labeled in eval-head. For those, use IH on depth + eval context stepping (one Flat step through .return/.yield wrapper, then IH on inner expression).

**Recommended approach**: Build `normalizeExpr_labeled_or_k` following the EXACT pattern of `normalizeExpr_tryCatch_or_k_aux` at L8062-8069. Then use it to eliminate impossible cases via exfalso, and handle remaining compound cases with IH.

### GROUP B: compound HasXInHead catch-all (4 sorries)
| L9387 | compound HasThrowInHead (seq_l, let_init, if_cond, call_callee, etc.) |
| L9544 | compound HasReturnInHead |
| L9721 | compound HasAwaitInHead |
| L9879 | compound HasYieldInHead |

These need eval context stepping: for each HasXInHead sub-constructor (seq_l, let_init, call_callee, etc.), one Flat step through the eval context, then IH.

### GROUP C: compound inner_val/inner_arg (3 sorries)
| L9538 | return compound inner_val (non-trivial cases like seq, let, etc.) |
| L9715 | await compound inner_arg |
| L9873 | yield compound inner_val |

### GROUP D: return/yield/compound (3 sorries)
| L9935 | return (some val) |
| L9939 | yield (some val) |
| L9940 | compound |

### GROUP E: while (2 sorries)
| L10030 | While condition value case |
| L10042 | Condition-steps case |

### GROUP F: tryCatch/call/break (6 sorries) — BLOCKED
| L12373 | tryCatch body-error |
| L12391 | tryCatch body-step |
| L13477 | noCallFrameReturn |
| L13488 | body_sim IH |
| L13708 | break |
| L13761 | continue |

## PRIORITY ORDER
1. **Build `normalizeExpr_labeled_or_k`** — unlocks ALL 7 Group A sorries
2. **GROUP A** (7 labeled) — use new lemma + IH for compound cases
3. **GROUP B** (4 compound HasXInHead) — eval context stepping per sub-constructor
4. **GROUP C** (3 inner_val/arg) — similar pattern
5. Everything else later

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
