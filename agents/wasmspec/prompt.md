# wasmspec — Close ANF deferred compound sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.4GB available right now.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS UPDATE: NoNestedAbrupt targets are DONE (proof agent closed them!)

Your previous targets (L9971-10005) were already proved by the proof agent. New targets below.

## NEW TARGETS: Deferred compound sorries (7 total)

These are throw/return/await/yield compound cases that all follow the same pattern. Each needs handling compound inner expressions (seq, let, assign, if, call, etc.) that have the relevant head constructor deeper inside.

### throw_step_sim compound (1 sorry):
- **L8523**: `sorry` — compound throw cases. `HasThrowInHead` compound constructors.

### return compound (2 sorries):
- **L8673**: `| _ => sorry -- compound inner_val: seq, let, assign, if, call, throw, etc.`
- **L8676**: `sorry -- compound HasReturnInHead cases`

### await compound (2 sorries):
- **L8846**: `| _ => sorry -- compound inner_arg: seq, let, assign, if, call, throw, etc.`
- **L8849**: `sorry`

### yield compound (2 sorries):
- **L9000**: `| _ => sorry -- compound inner_val: seq, let, assign, if, call, throw, etc.`
- **L9003**: `sorry -- compound HasYieldInHead cases`

### Pattern: These all share the same structure
When normalizeExpr produces a `.throw`/`.return`/`.await`/`.yield` and the expression has a HasXInHead compound constructor (like `seq_left`, `let_init`, `call_func`, etc.), we need to:
1. Take one Flat step to evaluate the compound sub-expression
2. Show the result still has the same head form
3. Apply the IH

The key challenge is "eval context lifting" — stepping through an evaluation context. If the expression is `seq (call f env args) rest` and HasThrowInHead says throw is in the call's sub-expression, we need to step `call f env args` first.

### Assessment approach:
1. Use `lean_goal` at each sorry to see what's actually needed
2. Check if there's existing infrastructure for eval context stepping
3. If one of them is close to provable, close it. If all are blocked on the same issue, document exactly what lemma is needed.

Even proving 1-2 of these is good progress.

## ALSO AVAILABLE: let/while step sim (2 sorries)
- **L9030**: `sorry -- Need characterization of what produces .let, flat simulation`
- **L9078**: `sorry` in while_ step sim

These might be easier. Use `lean_goal` to assess.

## DO NOT EDIT L9600-9775 or L10054-10200 (proof agent owns those regions)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
