# wasmspec — Investigate compound ANF sorries + error propagation semantics

## EXCELLENT WORK on CCStateAgree analysis — jsspec is implementing the fix NOW.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec is implementing CCStateAgree fix
- **DO NOT** edit ANFConvertCorrect.lean — proof agent owns it
- **DO NOT** run `lake build` anything
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.

## YOUR JOB: Three investigations for the proof agent

### Investigation 1: Error propagation through eval contexts (CRITICAL)

The proof agent needs to prove `hasBreakInHead_flat_error_steps` (L6608) and `hasContinueInHead_flat_error_steps` (L6621). These claim: if `HasBreakInHead e label`, then `e` flat-steps to `.lit .undefined` with break error trace.

THE PROBLEM: When `.break label` is nested inside `.seq (.break label) b`, Flat.step? produces `.seq (.lit .undefined) b`, NOT `.lit .undefined`. Then it steps to `b`, which is arbitrary.

Tasks:
1. Read `Flat.step?` definition in `VerifiedJS/Flat/Semantics.lean` (L336)
2. Trace what happens for EACH HasBreakInHead constructor (defined at ANFConvertCorrect.lean L2704):
   - `break_direct`: `.break label` → `.lit .undefined` ✓ (one step)
   - `seq_left`: `.seq (.break label) b` → `.seq (.lit .undefined) b` → `b` — does NOT produce `.lit .undefined`!
   - `seq_right`: `.seq a (.break label)` — needs `a` to evaluate first, may not terminate
   - `let_init`: `.let n (.break label) body` → `.let n (.lit .undefined) body` → what?
3. Determine: is `hasBreakInHead_flat_error_steps` PROVABLE as stated? Or does the statement need modification?
4. If unprovable, propose a corrected statement that IS provable and still useful at the call sites (L7755-8011)
5. Check call sites at L7755-8011: what do they actually NEED from this theorem?
6. Write findings to `agents/wasmspec/break_error_analysis.md`

### Investigation 2: "non-labeled inner value" sorry analysis

ANF has 4 sorries at L6401, L6434, L6530, L6563 labeled "non-labeled inner value: needs eval context lifting". These are `| _ => sorry` catch-all cases after `.labeled` is handled.

Tasks:
1. Use `lean_hover_info` or read the context around each sorry to understand what constructors remain in the `| _ =>` catch-all
2. Determine for each: is it closable by contradiction/exfalso (i.e., can those constructors actually reach this point given the normalizeExpr constraints)?
3. Write findings to `agents/wasmspec/non_labeled_analysis.md`

### Investigation 3: Compound stepping lemma patterns

8 of 22 ANF sorries are "compound" cases at L6774, L6777, L6927, L6930, L7100, L7103, L7254, L7257. These need eval context stepping when the inner expression is compound (seq, let, assign, if, call, etc.).

Tasks:
1. Read the context around L6774-6777 to understand the proof obligation
2. What existing eval context lemmas are available? (grep for `step?_.*_ctx` and `step?_.*_error`)
3. Is there a pattern where depth induction combined with existing lemmas can close these?
4. Write findings to `agents/wasmspec/compound_analysis.md`

### Step 1: Log start
```bash
echo "### $(date -Iseconds) Starting break error + non-labeled + compound analysis" >> agents/wasmspec/log.md
```

### Step 2: Do all three investigations (Investigation 1 is highest priority)

### Step 3: Log and EXIT
```bash
echo "### $(date -Iseconds) Run complete — [summary]" >> agents/wasmspec/log.md
```

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
