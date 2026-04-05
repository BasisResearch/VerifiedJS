# wasmspec — Close remaining sorries in normalizeExpr_if_branch_step zone

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.6GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11700+ (UNLOCK/compound_sim) and L12100+ (tryCatch, break/continue, call site)
- **YOU** own L1767-1950 (Steps_ctx_lift infrastructure) AND L8000-11650 (normalizeExpr_if_branch_step zone)
- DO NOT touch lines outside your range

## EXCELLENT WORK THIS CYCLE

You closed 16 hpres sorries AND started trivialChain decomposition (lit/var/this proved). ANF dropped from 56 to 40. Keep going!

## MEMORY WARNING: supervisor killed your lake build (parent process) to prevent OOM
Your lean child process (PID 697122) may still be running. If build completes, great. If it errors, re-check `ps aux | grep lake | grep -v grep | wc -l` before retrying.

## REMAINING SORRIES IN YOUR ZONE (6 confirmed):

**EXACT LINE NUMBERS (verified 17:30):**
- L11043: trivialChain seq case (true branch)
- L11094: trivialChain seq_right (true branch)
- L11201: exotic catch-all (true branch)
- L11366: trivialChain seq case (false branch)
- L11415: trivialChain seq_right (false branch)
- L11522: exotic catch-all (false branch)

### 1. trivialChain seq sorries (L11043, L11366)

**For var/this**: These should mirror the lit case you already proved. The pattern:
1. Evaluate the trivialChain var/this to get a value
2. One step to resolve var → lit v, then step through .if condition
3. Wire into the output

Use `lean_goal` at each sorry to see exact goal, then `lean_multi_attempt`.

### 2. seq_right (2 sorries) — ~L11147, ~L11512
- `.seq a b` where `HasIfInHead b` (not a)
- True branch ~L11147, false branch ~L11512

**Strategy**:
1. Check if a is a value (exprValue?)
2. If value: `.seq` steps to b, then IH on b
3. If not value: a must step (via trivialChain since ¬HasIfInHead a), lift through .seq, recurse

### 3. exotic cases (2 sorries) — ~L11254, ~L11619
- `| _ => sorry` catch-all for remaining HasIfInHead constructors

**TRY THIS FIRST**: Many exotic constructors may be impossible. Test:
```
lean_multi_attempt at the sorry line
["cases hif <;> simp_all [ANF.normalizeExpr] <;> sorry"]
```
If some constructors are impossible (normalizeExpr can't produce .if from that constructor), use `exfalso`.

For real cases: follow seq_left pattern (IH on sub-expression + Steps_*_ctx_b lift).

### 4. remaining inner case (~L11439)
This is in the false branch version, same class as the above.

## PRIORITY ORDER
1. Close var/this sorries — these are almost done from your lit proof
2. seq case in trivialChain
3. seq_right (2)
4. exotic — investigate which are contradictions
5. remaining false branch inner

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
