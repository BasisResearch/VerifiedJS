# proof — Close compound HasXInHead sorries (7 targets) + eval context (7 targets)

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L11053-11532 (trivialChain/exotic sorries)
- **YOU** own L8557-9940 (labeled/compound HasXInHead) AND L12375-13763 (tryCatch/call/break)
- DO NOT touch lines outside your range

## YOUR 32 SORRIES — CURRENT LINE NUMBERS (verified 18:30)

### GROUP A: eval context lifting (7 sorries, L8557-8743)
| L8557 | non-labeled inner value, eval ctx |
| L8590 | non-labeled inner value, eval ctx |
| L8601 | compound/bindComplex |
| L8682 | non-labeled inner value, eval ctx |
| L8715 | non-labeled inner value, eval ctx |
| L8726 | compound/bindComplex |
| L8743 | compound/bindComplex/throw/await |

### GROUP B: compound HasXInHead (7 sorries, L9387-9879) — PRIMARY TARGET
| L9387 | HasThrowInHead compound |
| L9538 | return compound inner_val |
| L9544 | HasReturnInHead compound |
| L9715 | await compound inner_arg |
| L9721 | HasAwaitInHead compound |
| L9873 | yield compound inner_val |
| L9879 | HasYieldInHead compound |

### GROUP C: return/yield/compound (3 sorries, L9935-9940)
| L9935 | return (some val) |
| L9939 | yield (some val) |
| L9940 | compound |

### GROUP D: while (2 sorries, L10030-10042)
### GROUP E: trivialChain/exotic (6 sorries, L11053-11532) — WASMSPEC OWNS THESE
### GROUP F: tryCatch/call/break (7 sorries, L12375-13763)

## STRATEGY FOR GROUP B (compound HasXInHead)

These all follow the SAME pattern. The expression `sf_expr` has `HasXInHead` but isn't a direct X — it's compound (seq, let, assign, if, call, etc.).

**For each case:**
1. The compound expression MUST step (one of its sub-expressions evaluates)
2. After stepping, HasXInHead is PRESERVED (the head still contains X)
3. Apply the normalizeExpr IH on the stepped state
4. Bridge to SimRel

**Start with L9387 (HasThrowInHead)**:
```
lean_goal at line 9387 column 4
```
Then try decomposing by the outer expression constructor:
```
lean_multi_attempt at line 9387 column 4
["cases sf_expr <;> simp_all [ANF.normalizeExpr] <;> sorry"]
```
Many sub-cases should be contradictions (exfalso via HasThrowInHead). For real cases (seq, let, call), use eval context stepping + IH.

## AFTER GROUP B: attack Group A (eval context lifting)
Group A cases need `Steps_*_ctx` infrastructure to lift inner steps through evaluation contexts. You already have `Steps_seq_left_ctx_b`, `Steps_if_cond_ctx_b`, etc. Apply the same pattern.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
