# proof — Close remaining 22 ANF sorries: compound inner_val (3) + eval ctx (4) FIRST

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
- wasmspec works on L11053-11425 (trivialChain seq sorries — only 4 left)
- **YOU** own everything else
- DO NOT touch lines 11053-11425

## GREAT WORK — 10 sorries closed this cycle!
You closed 8: compound/bindComplex (8601, 8726, 8743), HasThrowInHead (9387), HasReturnInHead (9544), HasAwaitInHead (9721), HasYieldInHead (9879), compound deferred (12394). Wasmspec closed 2 exotic catch-alls.

## YOUR 18 SORRIES — CURRENT LINE NUMBERS (verified 19:00)

### GROUP A: eval context lifting (4 sorries) — ATTACK THESE FIRST
| L8557 | non-labeled inner value, eval ctx |
| L8590 | non-labeled inner value, eval ctx |
| L8682 | non-labeled inner value, eval ctx |
| L8715 | non-labeled inner value, eval ctx |

These need `Steps_*_ctx` infrastructure to lift inner steps through evaluation contexts. You already have `Steps_seq_left_ctx_b`, `Steps_if_cond_ctx_b`, etc. Apply the same pattern you used for compound/bindComplex.

### GROUP B: compound inner_val/inner_arg (3 sorries) — HIGH PRIORITY
| L9538 | return compound inner_val |
| L9715 | await compound inner_arg |
| L9873 | yield compound inner_val |

These follow the SAME pattern as the HasXInHead sorries you just closed. The expression isn't a direct value — it's compound (seq, let, etc.). Decompose by outer expression constructor, use eval context stepping + IH.

### GROUP C: return/yield/compound (3 sorries)
| L9935 | return (some val) |
| L9939 | yield (some val) |
| L9940 | compound |

### GROUP D: while (2 sorries)
| L10030 | While condition value case |
| L10042 | Condition-steps case |

### GROUP E: trivialChain (4 sorries) — WASMSPEC OWNS THESE
| L11053 | trivialChain seq (true) |
| L11104 | seq_right (true) |
| L11376 | trivialChain seq (false) |
| L11425 | seq_right (false) |

### GROUP F: tryCatch/call/break (6 sorries)
| L12373 | tryCatch body-error |
| L12391 | tryCatch body-step |
| L13477 | noCallFrameReturn |
| L13488 | body_sim IH |
| L13708 | break |
| L13761 | continue |

## PRIORITY ORDER
1. **GROUP A** (4 eval ctx) — you have the infrastructure, these should be mechanical
2. **GROUP B** (3 compound inner_val) — same pattern as HasXInHead you just proved
3. **GROUP C** (3 return/yield/compound) — after A+B
4. Everything else later

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
