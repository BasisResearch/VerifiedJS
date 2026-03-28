# wasmspec — CLOSE return-some (L6801) THIS RUN

## STATUS: 15 actual Wasm sorries. Target: 14 (-1). return-some is GUARANTEED.

File: `VerifiedJS/Wasm/Semantics.lean`

## PRIORITY 0: return-some (L6801) — ALL 9 LEMMAS ALREADY PROVED

All 9 `step_sim_return_*` lemmas are fully proved (no sorry). You JUST need to dispatch.

**EXACT EDIT** — replace `| some t => sorry` at L6801 with:
```lean
        | some triv =>
          -- Dispatch to per-trivial-type lemmas (all proved above)
          cases triv with
          | litNull => exact step_sim_return_litNull prog irmod s1 s2 t s1' hrel hexpr hstep
          | litNum n => exact step_sim_return_litNum prog irmod s1 s2 t s1' hrel hexpr hstep
          | var name => exact step_sim_return_var prog irmod s1 s2 t s1' hrel hexpr hstep
          | litUndefined => exact step_sim_return_litUndefined prog irmod s1 s2 t s1' hrel hexpr hstep
          | litBool b =>
            cases b with
            | true => exact step_sim_return_litBoolTrue prog irmod s1 s2 t s1' hrel hexpr hstep
            | false => exact step_sim_return_litBoolFalse prog irmod s1 s2 t s1' hrel hexpr hstep
          | litObject addr => exact step_sim_return_litObject prog irmod s1 s2 t s1' hrel hexpr hstep
          | litStr s => exact step_sim_return_litStr prog irmod s1 s2 t s1' hrel hexpr hstep
          | litClosure fi ep => exact step_sim_return_litClosure prog irmod s1 s2 t s1' hrel hexpr hstep
```

**IMPORTANT**: The `| some t =>` at L6801 shadows the outer `t` (TraceEvent). You MUST rename it to `triv` (or any name). After `cases triv`, the outer `t` (TraceEvent) remains accessible for the lemma calls.

After the edit:
1. Rename `| some t =>` to `| some triv =>`
2. Add the cases block above
3. Build: `lake build VerifiedJS.Wasm.Semantics`
4. If type errors occur, check if `hexpr` has the right form. After match on `arg` then `cases triv`, `hexpr` should be `s1.expr = .return (some .litNull)` etc. If Lean doesn't propagate the match info, you may need `(hexpr ▸ rfl : s1.expr = .return (some .litNull))` or similar.

## PRIORITY 1: call case (L10776)

The call case was consolidated to a single sorry. Read L10777-10837 for the commented-out attempt. The main blockers are trap message alignment and multi-frame. Skip if return-some takes time.

## LSP TIMEOUT WORKAROUND
This file is 11K+ lines. Use `lean_diagnostic_messages` with start_line/end_line around edited area.

## Log to agents/wasmspec/log.md
