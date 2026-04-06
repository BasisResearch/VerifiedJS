# jsspec — ClosureConvertCorrect.lean (12 sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.

## MEMORY: ~1.5GB free. USE LSP ONLY.

## ===== YOUR PRIORITY: CC SORRIES (12 total) =====

All 12 sorry locations in ClosureConvertCorrect.lean:

```
L4905:  sorry                                    -- HeapInj refactor staging
L5234:  sorry⟩  -- CCStateAgree st' vs then_-only state
L5257:  sorry,  -- CCStateAgree threading
L5821:  sorry   -- non-consoleLog function call: funcs[idx] correspondence
L6029:  sorry   -- f not a value: Core allocates immediately but Flat steps f
L6037:  sorry   -- non-value arg: Core allocates immediately but Flat steps arg
L6675:  sorry   -- getIndex string both-values: UNPROVABLE
L7917:  sorry   -- functionDef: entire case
L8074:  sorry⟩  -- tryCatch body-value
L8075:  sorry   -- tryCatch body-value with finally: CCStateAgree blocked
L8147:  sorry   -- tryCatch sub-case
L8255:  sorry   -- while_ lowering: CCState threading
```

### Classification and action plan:

**POTENTIALLY PROVABLE (try these first):**

1. **L4905** — HeapInj refactor staging. Check git history for the previous proof. `lean_goal` to see what's needed. This was explicitly marked as restorable.

2. **L5821** — Non-consoleLog function call. Needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Check if there's a `convertFuncs` or similar lemma that establishes this. Use `lean_local_search` for "funcs" correspondence lemmas.

3. **L8147** — tryCatch sub-case. Use `lean_goal` to see the exact state. May be closeable with existing infrastructure.

**ARCHITECTURALLY BLOCKED (document but don't spin):**

4. **L5234, L5257** — CCStateAgree for if-true/false. Blocked because discarded branch's conversion changes nextId/funcs.size. Only provable if discarded branch has no `functionDef` nodes (which can't be assumed in general). Document this.

5. **L6029, L6037** — Core allocates immediately but Flat steps sub-expression. Multi-step simulation gap. Would need stuttering extension.

6. **L6675** — getIndex string both-values: explicitly marked UNPROVABLE.

7. **L7917** — functionDef: large case, likely needs significant infrastructure.

8. **L8074, L8075** — tryCatch body-value with/without finally: CCStateAgree blocked.

9. **L8255** — while_ lowering: CCState threading blocked.

### Workflow for each sorry:
1. `lean_goal` at the sorry line to see exact proof state
2. If provable: write the proof
3. If blocked: add a comment `-- BLOCKED: [reason]` and move on
4. Log your findings

### Key helper to look for:
Search for `CCStateAgree` definition and any monotonicity/threading lemmas:
```
lean_local_search "CCStateAgree"
lean_local_search "convertExpr_state"
lean_local_search "HeapInj"
```

## CONCURRENCY
- proof agent owns throw/return/await/yield zones in ANFConvertCorrect.lean
- wasmspec owns if_branch zones in ANFConvertCorrect.lean
- **YOU** own ClosureConvertCorrect.lean exclusively

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
