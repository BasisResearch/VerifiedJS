# wasmspec — YOU WERE ZOMBIE FOR 16+ HOURS. Fresh start.

## STEP 0: Verify your lean processes are NOT stuck

```bash
ps aux | grep -E "lean.*worker" | grep wasmspec
```

If ANY lean worker has been running for >30 minutes, kill it:
```bash
kill -9 <PID>
```

DO NOT run `lake build` until you confirm no stuck processes.

## YOUR TARGETS — 16 actual sorries in Wasm/Semantics.lean

jsspec is also working on Wasm now. To avoid conflicts:
- YOU work on L6798-L6819 (let, seq, if, while, throw, tryCatch) = 6 sorries
- jsspec is working on L6864-L6879 (return, yield, await, break, continue) + L6873 (labeled) = 6 sorries

### YOUR 6 TARGETS (sorted by difficulty):

1. **L6816** — throw: evaluate arg, produce error. Should be simple.
2. **L6806** — sequence: if a is value, skip to b; else step a
3. **L6798** — let binding: evaluate rhs, extend env, continue body
4. **L6810** — if/conditional: evaluate cond, branch
5. **L6819** — tryCatch: step body, catch errors, handle finally
6. **L6813** — while: loop body stepping

### APPROACH:
1. Read the PROVEN cases above L6798 (especially L6822-6863 for return-none) to learn the proof pattern
2. `lean_goal` at each sorry
3. `lean_multi_attempt` to test tactics
4. Edit the file to replace sorry when tactic works
5. `lake build VerifiedJS.Wasm.Semantics` after each edit
6. Max 20 min per sorry. If stuck, move on.

### HARD SORRIES (skip for now):
- L10857, L10912, L10916, L10919: call/callIndirect (complex)

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
## LOG every 15 min to agents/wasmspec/log.md
