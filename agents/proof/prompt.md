# proof — Close tryCatch subcases (L10204, L10272, L10275) — you're INSIDE the proof now

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.3GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L7700-9912 (if compound/eval context lifting)
- **YOU** own L10190-10278 (tryCatch) and L11560-11633 (break/continue)
- DO NOT touch lines outside your range

## GREAT PROGRESS — tryCatch lit-body/no-finally is PROVED

You decomposed tryCatch_direct beautifully. The lit-body no-finally case (L10206-10266) is fully proved. Now close the remaining 5 sorry subcases:

### TASK 1: L10272 — tryCatch body-error (PRIORITY 1)
```
sorry -- tryCatch body-error: needs inner body step simulation + catch handler SimRel
```
The ANF step? returned an error from the body. You need to:
1. `lean_goal` at L10272
2. The body is NOT a value, and step? body returned (.error msg, sb)
3. Show Flat.step? on the tryCatch also steps the body
4. When body errors, tryCatch catches it → steps to catch handler with error bound
5. Both ANF and Flat should do the same thing here
6. Use inner SimRel to get Flat stepping body → error, then tryCatch catches

### TASK 2: L10275 — tryCatch body-step (normal step)
```
sorry -- tryCatch body-step: needs inner body step simulation + tryCatch wrapping SimRel
```
1. Body takes a normal step (not error, not value)
2. ANF wraps stepped body back in tryCatch
3. Show Flat also steps body, wraps back in tryCatch
4. SimRel preserved because inner step preserves it

### TASK 3: L10204 — tryCatch body-value with finally
```
sorry -- tryCatch body-value with finally: Flat steps .tryCatch (.lit v) cp cb (some fin_f) → .seq fin_f (.lit v)
```
1. Body is a value, finally = some fin
2. ANF produces .seq fin (.trivial v)
3. Flat produces .seq fin_f (.lit v)
4. Construct SimRel between these

### TASK 4: L10232 — call frame case
This is likely contradictory in well-formed source programs. Try:
1. `lean_goal` at L10232
2. Show catchParam = "__call_frame_return__" contradicts source program well-formedness
3. If no well-formedness hyp available, add one or use `exfalso`

### TASK 5 (only if 1-4 done): L10278 — compound tryCatch cases
Deferred — needs eval context lifting (same blocker as ~17 other sorries).

## PRIORITY ORDER
1. L10272 (body-error) — should be most straightforward
2. L10275 (body-step) — similar pattern
3. L10204 (finally case)
4. L10232 (call frame contradiction)
5. L10278 (compound — only if time permits)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
