# jsspec — Fix 3 hne callers + CCStateAgree

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS: 15 sorries in CC. 3 are NEW error-propagation sorries.

## P0: FIX 3 ERROR-PROPAGATION SORRIES (BLOCKING)

These 3 sorries at L5090, L5182, L5420 were added for the `hne` argument to `Flat_step?_let_step`, `Flat_step?_assign_step`, `Flat_step?_seq_step`:

### L5090 — Flat_step?_let_step hne
```lean
(by intro msg hmsg; sorry) -- need: t ≠ .error msg
```
Context: `t` comes from `Flat.step?` matching `some (t, sa)`. Look at surrounding hypotheses — there should be `hsil` proving all events are `.silent`, or the match gives `t = .silent`.

**FIX**: Try each:
```lean
(by intro msg hmsg; subst hmsg; simp_all)
```
or:
```lean
(fun msg hmsg => by have := hsil t (List.mem_cons_self _ _); rw [this] at hmsg; exact Core.TraceEvent.noConfusion hmsg)
```
Use `lean_goal` at L5090 to see what hypotheses are available.

### L5182 — Flat_step?_assign_step hne
Same pattern. Fix with same approach.

### L5420 — Flat_step?_seq_step hne
Same pattern. Fix with same approach.

## P1: CCStateAgree (only after P0 is done)

Target sorries: L5261, L5287, L8115, L8192, L8308
These are all blocked by CCStateAgree (Blocker P). The viable fix is Path A: make `convertExpr` state-independent via position-based naming. This requires editing `ClosureConvert.lean` definitions — check with supervisor before attempting.

## Remaining CC sorries (12 total after P0):
- L4927: multi-step gap (Blocker T) — BLOCKED
- L5261, L5287: CCStateAgree if-branch — BLOCKED (Blocker P)
- L5855: FuncsCorr invariant — BLOCKED (Blocker Q)
- L6066, L6075: multi-step newObj gap — BLOCKED
- L6714: getIndex string — UNPROVABLE
- L7956: functionDef — BLOCKED (Blocker S)
- L8115, L8118: tryCatch — BLOCKED (Blocker P)
- L8192: CCStateAgree — BLOCKED (Blocker P)
- L8308: while_ CCState — BLOCKED (Blocker P)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — fixing 3 hne callers" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
