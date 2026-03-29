# wasmspec — YOU HAVE BEEN OOM FOR 28+ HOURS. RADICAL CHANGE.

## STATUS: 18 Wasm sorries. NO PROGRESS in 28+ hours. Multiple OOM kills (code 137, 143).

## THE PROBLEM: You keep attempting large proof sessions and getting killed.

## NEW MANDATE: ONE SORRY AT A TIME. BUILD AFTER EVERY CHANGE.

## PRIORITY 0: Identify the SINGLE easiest Wasm sorry

Read VerifiedJS/Wasm/Semantics.lean. Find the sorry that needs the FEWEST new lines to close.
Candidates (from grep):
- L6798, L6806, L6810, L6813, L6816, L6819 (step_sim cases)
- L6864, L6867, L6870, L6873, L6876, L6879 (more step_sim cases)
- L10857, L10912, L10916, L10919 (lower cases)

**Step 1**: Read 10 lines around EACH sorry. Score by difficulty (1=trivial, 5=hard).
**Step 2**: Pick the easiest one (score 1 or 2).
**Step 3**: Write the proof. MAX 20 lines.
**Step 4**: Build. If it passes, log and STOP.
**Step 5**: If it fails, sorry it back and try the NEXT easiest.

## CRITICAL CONSTRAINTS
- Edit < 30 lines per change
- `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
- Log after EVERY build (pass or fail)
- If any single task takes > 30 minutes, STOP and log what you learned
- Do NOT attempt hlabels_empty redesign (too large, will OOM)
- Do NOT attempt 1:N stepping framework (too large, will OOM)

## ALTERNATIVE: If ALL Wasm sorries are blocked

If after reading all 18, you determine none can be closed in < 30 lines, then:
1. Document WHY each is blocked (one line per sorry)
2. Identify the SMALLEST infrastructure change that unblocks the most sorries
3. Implement JUST that change (< 50 lines)
4. Build and log

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
## LOG: agents/wasmspec/log.md
