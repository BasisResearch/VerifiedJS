# wasmspec — Assist CCStateAgree implementation

## EXCELLENT WORK on the CCStateAgree analysis! That was the breakthrough we needed.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec is implementing your fix
- **DO NOT** edit ANFConvertCorrect.lean — proof agent owns it
- **DO NOT** run `lake build` anything
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.

## YOUR JOB: Support the CCStateAgree fix

jsspec is implementing the invariant change you proposed (dropping output CCStateAgree). Your job is to investigate the downstream impact:

### Step 1: Log start
```bash
echo "### $(date -Iseconds) Starting CCStateAgree support" >> agents/wasmspec/log.md
```

### Step 2: Find all uses of st_a' in the theorem body
Search for all places in ClosureConvertCorrect.lean that:
1. Construct `⟨st_a, st_a', ...⟩` (packing the existential)
2. Destructure `⟨..., st_a, st_a', hconv', hagree_in, hagree_out⟩` (unpacking)
3. Use `CCStateAgree st' st_a'` or `hagree_out`

Write the results to `agents/wasmspec/ccstateagree_uses.md` with exact line numbers.

### Step 3: Identify which cases use output agreement
For each case in the big theorem body, classify:
- **Needs output agreement**: The case's proof uses `hagree_out` from the IH result
- **Doesn't need output agreement**: The case only uses `st_a` and `hagree_in`

This tells jsspec exactly which cases are easy (just delete st_a') and which need rework.

### Step 4: Draft the standalone sub-stepping lemma
For cases that DO need output agreement, draft:
```lean
theorem convertExpr_subStep_output_agree
  (hAgree : CCStateAgree st st_a)
  (hstep : -- sub-expression steps, preserving structure)
  : CCStateAgree (convertExpr e scope envVar envMap st).snd
                  (convertExpr e' scope envVar envMap st_a).snd
```

### Step 5: Log and EXIT
```bash
echo "### $(date -Iseconds) Run complete — CCStateAgree uses mapped" >> agents/wasmspec/log.md
```

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
