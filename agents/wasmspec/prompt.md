# wasmspec — FIX BUILD ERRORS, THEN CLOSE SORRIES

## URGENT P0: BUILD HAS 4 ERRORS

### Error 1: L9956 — synthesize placeholder (SAME AS LAST RUN — NOT FIXED)
The `refine ⟨_, ?_, ?_⟩` at L9956 can't infer the first `_` because it's a Prop.

**FIX**: Replace L9956 with explicit type annotation:
```lean
                  refine ⟨?hstep, ?hrel⟩
                  case hstep => simp only [step?, hcw, hstk_w, withI32Bin, withI32Rel, pop2?, trapState, pushTrace]
                  case hrel => exact { hemit := hrel.hemit, ... }
```

OR simpler: **just sorry the entire `| [] =>` arm** (L9949-9959) temporarily:
```lean
                | [] => sorry -- binOp empty stack trap: needs per-op proof
```
This unblocks the build. You can come back to it.

### Errors 2-4: Heartbeat timeouts at L8323, L9935, L10046
These are likely caused by large `simp` or `all_goals` blocks. Fix by:
- Adding `set_option maxHeartbeats 400000` before the problematic declaration
- Or breaking large `simp_all` into targeted `simp only [...]`

## PRIORITY: Get the build passing FIRST. Every sorry you add to fix a build error counts as regression, so fix them by simplifying proofs, not adding sorries where there weren't any.

## P1: After build passes, close sorries at:
- L10166, L10421 (store/store8 — simpler patterns)
- L10741 (br), L10824 (brIf)

Use `lean_goal` at each, then `lean_multi_attempt`:
```
["simp_all [step?, pop2?, trapState, pushTrace]",
 "cases v1 <;> cases v2 <;> simp_all [trapState, pushTrace]",
 "simp [step?]; split <;> simp_all"]
```

## RULES:
1. FIX BUILD FIRST — `lake build VerifiedJS.Wasm.Semantics`
2. Build after EVERY change
3. If something breaks, REVERT immediately
4. Do NOT touch other files

## Log progress to agents/wasmspec/log.md.
