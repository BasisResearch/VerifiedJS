# jsspec — ClosureConvertCorrect.lean (12 sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: Rate limits blocked all agents for 18 hours. Fresh start.

## ===== YOUR 12 SORRIES =====

```
L4905:  sorry                    -- HeapInj refactor staging (RESTORABLE from git)
L5234:  sorry⟩                   -- CCStateAgree st' (if-then branch)
L5257:  sorry,                   -- CCStateAgree threading (if-else branch)
L5821:  sorry                    -- non-consoleLog function call: funcs[idx] correspondence
L6029:  sorry                    -- f not a value: Core allocates, Flat steps f
L6037:  sorry                    -- non-value arg: Core allocates, Flat steps arg
L6675:  sorry                    -- getIndex string both-values: UNPROVABLE
L7917:  sorry                    -- functionDef: entire case
L8074:  sorry⟩                   -- tryCatch body-value
L8075:  sorry                    -- tryCatch body-value with finally
L8147:  sorry                    -- tryCatch sub-case
L8255:  sorry                    -- while_ lowering: CCState threading
```

## ===== PRIORITY ORDER =====

### P0: L4905 — HeapInj refactor staging (HIGHEST PRIORITY)
This was explicitly marked as restorable from git history. Steps:
1. `lean_goal` at L4905 to see the exact proof state
2. `git log --oneline -20 -- VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find the commit with the previous proof
3. Restore the proof from history if possible
4. If the types have changed, adapt the old proof to the new types

### P1: L5821 — non-consoleLog function call
Needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Steps:
1. `lean_goal` at L5821
2. `lean_local_search "funcs"` or `lean_local_search "convertFuncs"` to find helper lemmas
3. Build the proof from the correspondence

### P2: L8147 — tryCatch sub-case
1. `lean_goal` at L8147
2. May be closeable with existing infrastructure

### SKIP THESE (architecturally blocked):
- L5234, L5257 — CCStateAgree blocked by discarded branch's nextId/funcs.size change
- L6029, L6037 — Multi-step simulation gap (stuttering)
- L6675 — Explicitly marked UNPROVABLE
- L7917 — Large case needing significant infrastructure
- L8074, L8075 — CCStateAgree blocked
- L8255 — CCState threading blocked

## WORKFLOW
1. `lean_goal` at the sorry
2. `lean_multi_attempt` to test tactics
3. Edit to replace sorry
4. `lean_diagnostic_messages` to verify
5. Move to next sorry

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
