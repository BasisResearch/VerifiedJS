# proof — CC CCSTATE THREADING: USE Prod.mk.eta

## STATUS: 62 grep sorries (17 ANF + 27 CC + 18 Wasm + 0 Lower).

## PRIORITY 0: CC CCState threading at L2383, L2405, L3703

The CC_SimRel (L1098-1099) requires:
```lean
∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st
```

### L2383 (if-true CCState threading)

The sorry is the last element of:
```lean
· exact ⟨st, (Flat.convertExpr then_ scope envVar envMap st).snd, by
    simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, sorry⟩
```

**First**: use `lean_goal` at L2383 to check what the goal actually is.

The CCState witness for the then_ sub-expression after if-true stepping:
- sc'.expr = then_
- sf'.expr = (convertExpr then_ scope envVar envMap st).fst
- So the witness should be: st_start = st, st_end = (convertExpr then_ scope envVar envMap st).snd
- The equality `(sf'.expr, st_end) = convertExpr then_ scope envVar envMap st` follows from `Prod.mk.eta`

Try replacing the sorry with:
```lean
exact Prod.ext (congrArg Prod.fst <| by simp [sc', Flat.convertExpr]) (congrArg Prod.snd <| by simp [sc', Flat.convertExpr])
```

Or if the sorry is about something else (AgreeOut?), use `lean_goal` first.

### L2405 (if-false CCState threading)

Same pattern but for else_ branch. The witnesses are:
- st_start = (convertExpr then_ scope envVar envMap st).snd
- st_end = (convertExpr else_ scope envVar envMap st_start).snd

Two sorries here: one is the conversion equality, one might be the AgreeOut.

### L3703 (while_ CCState threading)

while_ duplicates cond+body. Use `convertExpr_state_determined` (L548) to show
the duplicated conversion produces CCStateAgree results.

## PRIORITY 1: Check forIn/forOf sorries (L1148-1149)

These are in `convertExpr_not_value`. The comment says "theorem false" — if that's literally true (forIn/forOf are stubs that convert to `.lit .undefined` which HAS a value), then these cannot be closed. But check: does the hypothesis `h : Core.exprValue? e = none` for `e = .forIn ...` actually hold? If forIn is never used in the supported subset, maybe we need `h_supported` to exclude these cases.

## PRIORITY 2: Do NOT attempt ANF sorries

Proof agent's own analysis (log 2026-03-28T11:30) showed these are fundamentally blocked by:
- Nesting contamination
- Eval-context lifting lemmas not yet written
- 4 permanently unprovable (throw/return/break/continue semantic mismatches)

## WORKFLOW
1. `lean_goal` at each sorry BEFORE attempting anything
2. `lean_multi_attempt` to test candidate tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build fails, sorry it back IMMEDIATELY

## FILES: `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
