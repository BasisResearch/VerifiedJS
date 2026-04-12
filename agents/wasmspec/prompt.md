# wasmspec — CLOSE noCallFrameReturn PRESERVATION + INITIAL STATE

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T03:05
- Total: **47 real sorries** (ANF 35, CC 12). DOWN from 63 last run. -16!
- Bridge lemma is PROVED. Two new sorries remain: L27149 (preservation) + L27184 (initial state).
- P1 (HasNonCallFrameTryCatch L17436) is BLOCKED per your analysis — predicate too strong.

## P0: noCallFrameReturn PRESERVATION (L27149) — HIGHEST PRIORITY

Goal: `noCallFrameReturn sf2.expr = true` where sf2 comes from flat steps simulating one ANF step.

### Approach: prove noCallFrameReturn_step_preserved
```lean
theorem noCallFrameReturn_step_preserved
    (hncfr : noCallFrameReturn sf.expr = true)
    (hstep : Flat.step? sf = some (t, sf')) :
    noCallFrameReturn sf'.expr = true
```

Proof strategy — case split on `Flat.step?`:
- **Value/literal cases**: result is value, trivially noCallFrameReturn
- **Seq/let/if/etc**: structural — sub-expression stepped, rest unchanged
- **Call**: post-call result is `.lit v` (value), trivially noCallFrameReturn
- **TryCatch**: only introduces `__call_frame_return__` for call-frame tryCatch,
  which is excluded by `noCallFrameReturn`. Non-call-frame tryCatch preserves the property.

Then extend to multi-step with `noCallFrameReturn_steps_preserved`.
Apply at L27149.

**Expected: -1 sorry**

## P1: noCallFrameReturn INITIAL STATE (L27184)

Goal: `noCallFrameReturn (initialState program).expr = true` or similar.

Source programs never use `"__call_frame_return__"` as a tryCatch catchParam because:
- It's a compiler-generated name (starts with `__`)
- Source programs only have user-written catch parameter names
- The `compile` function introduces `__call_frame_return__` ONLY during lowering

Prove: source expressions have `noCallFrameReturn = true` by structural induction on the AST.

**Expected: -1 sorry**

## P2: HasNonCallFrameTryCatch — REDESIGN NEEDED (L17436)

Your analysis showed the predicate is too strong. If you have time:
- Define `HasNonCallFrameTryCatchInEvalFirst` that only checks eval-first positions
- This is a bigger change (~700 lines per your estimate). Only attempt if P0+P1 done quickly.

## P3: L26229, L26300 — check what's needed
`lean_goal` at these. May be closeable.

## DO NOT WORK ON:
- L11186-L11557 (labeled trivial mismatch — proof agent, BLOCKED)
- ClosureConvertCorrect.lean (jsspec)
- L15136-L15190 (proof agent HasThrowInHead infrastructure)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — noCallFrameReturn preservation + initial" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
