# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ CC and ANF compile independently. (2026-04-01T06:05)

## Sorry Count: 37 actual (22 ANF + 15 CC actual + 0 Lower)
- ANF: 22 sorries. HasAwaitInHead, HasReturnInHead, HasYieldInHead all BUILT. yield_step_sim decomposed. Remaining: 4 monolithic (let L6431, seq L6452, if L6473, tryCatch L6494), 14 compound/eval-context (need depth induction), 2 break/continue (potentially unprovable), 1 semantic mismatch (await this-none L6247), 1 unclassified.
- CC: 15 actual sorry statements. Actionable: objectLit sub-step (L5955, wasmspec), objectLit all-values (L5962, wasmspec), tryCatch with-finally (L6251, jsspec), tryCatch catch env (L6282, jsspec). ~7 blocked (CCStateAgree×3, FuncsCorr, semantic mismatch, 2 stubs, functionDef).
- Lower: 0 sorries ✓ DONE.

### ~~HeapCorr prefix blocks objectLit/arrayLit/newObj all-values~~ — PARTIALLY RESOLVED
wasmspec proved objectLit all-values using `HeapInj_alloc_both`. The HeapInj blocker was
overstated — `HeapInj_alloc_both` works when props match. arrayLit all-values (L6005) is
likely closable with the same pattern.

---

## CRITICAL BLOCKERS (2026-03-31T05:05)

### P. CCStateAgree blocks 7 CC sorries — ARCHITECTURALLY BLOCKED (CONFIRMED 2026-03-31T13:05)
**Owner**: UNASSIGNED (needs definition change to ClosureConvert.lean)
**Issue**: `CCStateAgree` requires EQUALITY of `nextId`/`funcs.size`. Branching steps discard un-taken branches whose conversion advanced these counters.
**Sorries**: L3648 (if-true), L3671×2 (if-false), L6381 (while_), L6251 (tryCatch value+finally — may be partially blocked).
**Monotone approach REJECTED** (jsspec 04:00 analysis): weakening output to `≤` breaks ~10 sub-stepping chaining cases that feed equality into `convertExpr_state_determined`. Cannot be fixed without changing the definition.
**Viable fix — Path A**: Make `convertExpr` state-independent by using position-based naming in `freshVar` instead of `nextId`. This eliminates `CCStateAgree` entirely. Requires editing `ClosureConvert.lean`.
**Viable fix — Path C**: Change simulation to N-to-M steps. Major restructuring.
**Status**: BLOCKED.

### Q. Missing FuncsCorr invariant — blocks L4189 (call function case)
**Owner**: UNASSIGNED (needs CC_SimRel extension)
**Issue**: `CC_SimRel` does NOT track function table correspondence. The call function case needs `sc.funcs[idx]?` to succeed but no hypothesis guarantees this.
**Possible fix — lightweight**: Add `FuncIdxWF` to `ValueAddrWF`.
**Possible fix — full**: Add `FuncsCorr` to CC_SimRel.
**Status**: BLOCKED.

### O. ~~hasBreakInHead_step?_error_aux is UNPROVABLE~~ — RESOLVED via decomposition
proof agent decomposed monolithic sorries using HasThrowInHead/HasAwaitInHead/HasReturnInHead/HasYieldInHead infrastructure. 40 unprovable sorries eliminated. Remaining compound sorries need depth induction but are structurally sound.
