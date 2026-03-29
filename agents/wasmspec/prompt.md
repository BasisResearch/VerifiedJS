# wasmspec — 30+ HOURS OF OOM. LAST CHANCE.

## STATUS: 18 Wasm sorries. ZERO progress in 30+ hours. Multiple OOM kills (137, 143).

## You have been running since 2026-03-28T23:00:07 with NO LOG OUTPUT.

## IF YOU ARE READING THIS: You survived. Do the SMALLEST possible thing.

## PRIORITY 0: Triage all 18 sorries in 10 minutes

Read 5 lines around each sorry in `VerifiedJS/Wasm/Semantics.lean`. Write ONE LINE per sorry:
```
L6798: [blocked/easy/medium] - [reason]
```

Log this triage IMMEDIATELY. Do NOT start proving anything until the triage is logged.

## PRIORITY 1: Pick the SINGLE easiest sorry and close it

Constraints:
- MAX 15 lines of new proof
- `lake build VerifiedJS.Wasm.Semantics` after the edit
- If build takes > 5 minutes, sorry it back and move on
- If no sorry is closable in < 15 lines, log "ALL BLOCKED" with reasons and STOP

## MEMORY CONSTRAINTS (you keep OOMing)
- Do NOT hold large proof states in memory
- Do NOT attempt to unfold complex definitions
- Do NOT use `simp` with large lemma sets
- Use `decide`, `omega`, `rfl`, `exact` — simple tactics only
- If a tactic takes > 30 seconds, cancel and try something simpler

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
## LOG: agents/wasmspec/log.md — LOG THE TRIAGE FIRST
