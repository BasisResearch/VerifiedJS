# proof — ANF COMPOUND CASES + WHILE/IF/TRYCATCH

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T13:05
- **Break list + continue second-operand + continue list: ALL CLOSED** (19 sorries eliminated)
- ANF down to **29 real sorry lines** (was ~48)
- 12 of those are BLOCKED (L11366-L11737) — DO NOT TOUCH
- 2 are wasmspec-owned — DO NOT TOUCH
- **YOUR TARGET: 15 remaining sorry lines**

## P0: COMPOUND AWAIT/YIELD/RETURN (5 sorries)
- **L24663**: compound HasAwaitInHead — blocked by Flat.step? error propagation
- **L24836**: compound HasYieldInHead — blocked by Flat.step? error propagation
- **L24892**: return (some val) compound — can produce .let
- **L24896**: yield (some val) compound — can produce .let
- **L24897**: compound expressions (seq, let, assign, if, call, etc.)

These are all blocked by the same issue: error propagation through Flat.step?
The blocking infrastructure is at L11763. If you can prove ONE case, the rest follow the same pattern.

### Strategy for L24892 (return some val):
1. `lean_goal` at L24892 to see the proof state
2. The return (some val) case produces `.let` when val is compound
3. Need to show the ANF normalizeExpr of `.return (some val)` corresponds to evaluating val first, then returning
4. Check if `normalizeExpr_return_some_or_k` gives the needed lemma

## P1: WHILE CONDITION (2 sorries)
- **L24987**: While condition value case — transient state breaks single-step SimRel
- **L24999**: Condition-steps case — needs flat while-condition simulation

### Strategy:
These need a while-specific simulation approach. The while unfolds to:
`.if cond (.seq body (.while_ cond body)) (.lit .undefined)`
The condition evaluation creates a transient state that doesn't match the SimRel.

Try `lean_multi_attempt` with:
```
["exact while_cond_value_sim hcond_val hstep",
 "apply while_cond_step_sim hcond_step",
 "sorry"]
```

## P2: IF-BRANCH (2 sorries)
- **L25724**: if_branch true — collapsed (24 sub-cases, K-mismatch)
- **L25764**: if_branch false — collapsed (24 sub-cases, K-mismatch)

These were collapsed into single sorries to avoid OOM. The K-mismatch means the
continuation `k` from normalizeExpr doesn't match between the source and target.

## P3: TRYCATCH (3 sorries)
- **L26605**: tryCatch body-error — lifting body steps through tryCatch context
- **L26623**: tryCatch body-step — callStack propagation + counter alignment
- **L26626**: compound cases — deferred

## P4: body_sim IH (1 sorry — L31484)
- Needs anfConvert_step_star to be proved by strong induction
- This is a RECURSIVE dependency — skip until P0-P3 are done

## BLOCKED (12): L11366-L11737 — DO NOT TOUCH
## WASMSPEC-OWNED: L18163, L19377, L32642, L32673 — DO NOT TOUCH

## EXECUTION ORDER:
1. Start with P0 L24892 (return some val) — most tractable compound case
2. If blocked, try P1 L24987 (while condition value)
3. Then P2 (if-branch)
4. P3 (trycatch) last

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
