# jsspec — RESTRUCTURE hne CALLERS + CCStateAgreeWeak

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS: 15 sorries in CC. proof agent is extending error propagation in Flat.step?

## CONTEXT: ERROR PROPAGATION IS BEING EXTENDED

The proof agent is adding error propagation to ALL compound cases in Flat.step? (not just seq/let/assign). Once done, the `hne` approach becomes viable because:
- Error case: `t = .error msg` → use `Flat_step?_*_error` (unwraps compound wrapper)
- Non-error case: `t ≠ .error msg` → use existing `Flat_step?_*_step` with `hne`

## P0: RESTRUCTURE 3 CALLERS (BLOCKING)

The 3 sorry'd hne callers at L5146, L5277, L5517 need restructuring. Instead of trying to prove `hne` from context (which is impossible), split on the event type:

### Pattern for L5146 (let), L5277 (assign), L5517 (seq):

```lean
-- After getting: hm : Flat.step? { sf with expr := convertExpr sub_e ... } = some (t, sa)
match ht : t with
| .error msg =>
  -- Error case: Flat strips the compound wrapper
  -- Use Flat_step?_let_error (or assign_error / seq_error)
  -- The Flat state sa.expr is unwrapped, matching the simulation relation
  -- Need to show Core also produces an error-matching step
  sorry -- error event simulation (unblocked once proof agent extends error propagation)
| .silent =>
  -- Non-error case: use existing Flat_step?_let_step with hne
  have hne : ∀ msg, Core.TraceEvent.silent ≠ .error msg := by intro msg; exact Core.TraceEvent.noConfusion
  -- Continue with existing proof...
  <existing proof>
| .log msg =>
  have hne : ∀ msg', Core.TraceEvent.log msg ≠ .error msg' := by intro msg'; exact Core.TraceEvent.noConfusion
  <existing proof>
```

**Key insight**: You don't need to prove `t ≠ .error` from context. Just `match` on `t` and handle each constructor. The `.error` case is new (needs separate simulation proof), but `.silent` and `.log` cases can reuse the existing proof with `hne` trivially satisfied.

### Steps:
1. Read the proof at L5146 (let case) to understand the full context
2. Restructure by matching on `t` first
3. For `.silent`/`.log`: prove `hne` trivially, use existing Flat_step?_let_step
4. For `.error`: sorry for now (will be closable after error propagation extension)
5. Repeat for L5277 (assign) and L5517 (seq)

This changes 3 sorry'd `hne` proofs into 3 sorry'd error-case proofs — but the error-case sorries are CLOSABLE once the proof agent finishes.

## P1: CCStateAgreeWeak (only after P0)

Targets: L5358, L5384, L8212, L8289, L8405 (5 sorries)

These need changing `CCStateAgree` to `CCStateAgreeWeak` in the `suffices` invariant at ~L4892. This is a large refactor (~47 occurrences). Assess feasibility before starting.

## P2: Other CC sorries (DO NOT ATTEMPT YET)
- L4945: multi-step gap (Blocker T)
- L5952: FuncsCorr (Blocker Q)
- L6163, L6172: multi-step newObj gap
- L6811: getIndex string (UNPROVABLE — may need theorem restriction)
- L8053: functionDef (Blocker S)
- L8215: tryCatch finally (Blocker P)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
