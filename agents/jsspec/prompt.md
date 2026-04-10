# jsspec — Fix CC callers + CCStateAgree

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: Flat_step? theorems FIXED but callers NOT updated

You already added `(hne : ∀ msg, t ≠ .error msg)` to:
- `Flat_step?_assign_step` (L1963)
- `Flat_step?_seq_step` (L2215)
- `Flat_step?_let_step` (L2245)

And added `Flat_step?_seq_error` companion (L2223).

**BUT the callers are NOT updated.** They still call without the `hne` argument.

## ===== P0: FIX ALL 3 CALLERS — BLOCKING EVERYTHING =====

### Caller 1: L5087-5089 — Flat_step?_let_step in let case
```lean
have heq := Flat_step?_let_step sf name
    (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst
    _ hfnv t sa hm
```
**Missing**: `hne` argument after `hm`. The `t` comes from `| some (t, sa) =>` match on `Flat.step?`. In this context, you need to prove `t` is not an error. Look at the surrounding hypothesis — there should be `hsil` or similar proving all events are silent.

**FIX**: Add proof after `hm`:
```lean
    _ hfnv t sa hm (fun msg hmsg => by ...)
```
Use `lean_goal` at this position to see what's available. Likely `hsil` or the match guard gives `t = .silent`.

### Caller 2: L5180 — Flat_step?_assign_step
```lean
have heq := Flat_step?_assign_step sf name _ hfnv t sa hm
```
**FIX**: Add `(fun msg hmsg => by ...)` after `hm`.

### Caller 3: L5415 — Flat_step?_seq_step
```lean
have heq := Flat_step?_seq_step sf ... _ hfnv t sa hm
```
**FIX**: Add `(fun msg hmsg => by ...)` after `hm`.

### How to prove hne at each call site
At each call site, `t` comes from matching `Flat.step?` result. The surrounding proof context should have one of:
- `hsil : ∀ ev ∈ evs, ev = .silent` — then `t` is forced silent
- Direct match showing `t` is `.silent`
- Non-error guard on the flat step

Use `lean_goal` at each call site to find the right hypothesis. Then:
```lean
(fun msg hmsg => by subst hmsg; simp_all)
```
or:
```lean
(fun msg hmsg => by exact Core.TraceEvent.noConfusion (hsil t ▸ hmsg))
```

## ===== P1: CCStateAgree (only after P0 is clean) =====

Target sorries: L8189, L8305
These need CCStateAgreeWeak — a weakened version of CCStateAgree that allows nextId/funcs.size to differ between branches. See previous analysis.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — fixing CC callers" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
