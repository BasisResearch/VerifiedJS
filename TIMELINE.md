# VerifiedJS Agent Timeline — 30 Hours of Autonomous Compiler Verification

## The Setup (March 20, ~14:00 UTC)

Fresh Ubuntu 24.04 server at proof.kirancodes.me. Nginx + Let's Encrypt SSL. The VerifiedJS compiler — a formally verified JS-to-Wasm compiler in Lean 4 — was already functional: it could parse JS, lower through 6 intermediate languages, and emit working WebAssembly. 8/10 handwritten e2e tests passing. 12 `sorry` holes in the proofs. ~13,000 lines of Lean.

Four Linux users created: `jsspec`, `wasmspec`, `proof`, `supervisor`. Each can only write files they own (enforced by Unix permissions). A cron job spawns each agent hourly. The agents are Claude Code instances running `--dangerously-skip-permissions` with the Lean LSP MCP server for proof assistance.

---

## Hour 0–1: The Golden Hour (16:30–17:30 UTC)

**All four agents wake up simultaneously.** This is their most productive period.

**jsspec** (16:31–16:51): Implements semantics for 6 major JS constructs in a single 20-minute run:
- try/catch/finally (ECMA-262 §13.15)
- typeof (§12.5.6)
- return/break/continue (§13.1/§13.6/§13.8)
- function calls with argument evaluation (§13.3.1)
- property access (getProp, getIndex) with heap lookup (§12.3.2)
- function definitions, object literals, array literals

Adds 4 e2e tests. E2E: 16/17 passing. Notes Wasm lowering gaps "outside owned files" — a recurring theme.

**proof** (16:33–16:52): Goes from 11 sorries to 6 in one run. Proves three Lower theorems (`lower_startFunc_none`, `lower_exports_shape`, `lower_memory_shape`). Implements `Wasm.interp` — a fuel-based interpreter. Then writes a remarkably prescient blocker analysis:

> "All 6 remaining sorries are BLOCKED by two architectural issues: (1) step? is partial def, making it opaque to Lean's proof system (2) Overly-strong universals — step_simulation quantifies over ALL states, not just reachable ones"

This diagnosis is correct and will take 10+ hours to resolve.

**proof** immediately runs again (16:57–17:12): Restructures both ClosureConvertCorrect and ANFConvertCorrect to use simulation relations (`CC_SimRel`, `ANF_SimRel`). Goes from 6 sorries to 4. Proves `steps_simulation` and `trace_reflection` for both passes. Identifies the remaining blocker:

> "Recommended fix for jsspec: Make step? non-partial using termination_by sizeOf s.expr"

**wasmspec** starts working on the if-label fix in Wasm semantics, adds validation and typing rules.

---

## Hour 1–2: The Breakthrough Run (17:15–18:15 UTC)

**proof** (17:17–18:13): Can't prove the remaining 4 sorries (blocked on partial def), so pivots to something it CAN do — implements a massive Wasm runtime:
- `__rt_typeof` — NaN-boxing tag dispatch
- `__rt_printValue` — full type dispatch for console.log
- `__rt_objectLit`, `__rt_construct`, `__rt_setProp`, `__rt_getProp` — heap allocation + property access
- Global string table with interning
- `i64.extend_i32_s/u`, `i32.ge_u/gt_u/lt_u/le_u` in the emitter

**E2E goes from 17/21 to 25/30** — the proof agent single-handedly fixed 8 failing tests by implementing the runtime helpers that the compiler needs to actually run JS programs.

**jsspec** (16:56–17:04): Adds for-in/for-of, setProp/setIndex, deleteProp, newObj, instanceof, modulo, exponentiation, bitwise stubs. E2E: 17/21.

**jsspec** (17:16–17:40): Adds bitwise operators, getIndex heap lookup, object/array literal evaluation, yield/await stubs, string coercion. Then makes a critical announcement:

> "Achievement: Removed wildcard fallthrough in step? — ALL Core Expr constructors now have explicit step cases. This is important for provability: no constructs silently fail with 'unimplemented'"

But also notes: "Full build BLOCKED by wasmspec agent breaking ANF/Semantics.lean (removed `partial` without valid termination proof)"

**This is the first inter-agent breakage.** wasmspec tried to make step? non-partial (following the proof agent's recommendation) but got the termination proof wrong.

---

## Hour 2–3: Cross-Agent Coordination (18:00–19:30 UTC)

**jsspec** (18:00): Implements full function closure semantics — captures, call stack, environment restoration. Adds abstract equality, string comparison, console.log built-in. E2E: 32/37.

**proof** (18:30–19:30): Implements logical operators (`||`, `&&`), recursive function calls, function index offsets, nested function support. E2E: 34/37.

**supervisor** runs its first assessment. Notes the sorry plateau at 4 and that the proof agent has been productive despite being blocked.

---

## Hour 4–6: The Partial Def Fix (20:30–22:50 UTC)

**jsspec** (20:32–20:40): THE KEY MOMENT. Implements the fix that the proof agent requested 4 hours earlier:

> "Changed `partial def step?` → `def step?` with `termination_by s.expr.depth`"

Adds `Expr.depth`, `firstNonValueExpr_depth` theorem, extracts helper functions. This unblocks 2 of the 4 remaining sorries. E2E: 40/43.

But then notes a new problem: "wasmspec agent broke .lake/packages/duper — cloned with wrong permissions and wrong Lean version."

**Meanwhile, infrastructure chaos**: The human operator removes Duper and Canonical from the lakefile (they were broken), does a full `lake clean && lake update`, and rebuilds. The agents receive system notes in their logs.

---

## Hour 6–12: The Test Explosion (22:50–06:00 UTC, overnight)

jsspec enters a test-writing frenzy. The human told it to focus on e2e tests, and it takes this literally.

**jsspec** (00:00–00:30): Adds 26 new e2e tests. Adds 5 proof theorems (step_deterministic, Steps_trans, etc.). E2E: 74/77. Also fixes String.trim deprecation.

**jsspec** (01:00–01:35): Adds 10 more tests, 7 more proof theorems (Steps_single, evalBinary_total, etc.). E2E: 84/87.

**jsspec** (02:00–02:15): Adds 22 proof theorems and 18 tests. E2E: 102/105. The Core semantics file is growing rapidly.

**jsspec** (03:00–03:10): Adds 40 proof theorems and 18 tests. E2E: 120/123. Total Core proof theorems: 74.

**proof** (00:03–00:51): Fixes the broken ANFConvertCorrect.lean. Restructures both proof files with stronger simulation relations. Fixes indirect call type mismatch in Emit.lean. E2E: 74/77. Makes `convertExpr` non-partial, makes `normalizeExpr` public. Strengthens both `CC_SimRel` and `ANF_SimRel` to include expression correspondence.

**proof** (01:30–02:13): Proves 7+ constructor cases of halt_preservation. Discovers a genuine falsity:

> "forIn and forOf in halt_preservation — convertExpr maps them to .lit .undefined (halts in Flat) but Core.step? returns some (steps). Theorem is false for unimplemented features."

This is a real mathematical discovery — the theorem statement is false for stubbed features.

**wasmspec** (04:15–06:15): Adds trace event mappings between Core/IR/Wasm. Implements complete i32/i64/f64 binary+unary ops. Adds cross-type conversion ops. Adds 14 exact-value equation lemmas for irStep?. Makes `valuesFromExprList?` public — directly unblocking the proof agent.

---

## Hour 12–18: Auth Crisis & Simp Loop (06:00–14:00 UTC)

**Auth tokens expire.** All four agents start failing with "Not logged in" errors. Every hourly cron run exits code 1 in under 5 seconds. This continues for ~8 hours until the human notices and refreshes tokens.

```
## Run: 2026-03-21T08:00:01+00:00
2026-03-21T08:00:05+00:00 EXIT: code 1
## Run: 2026-03-21T09:00:01+00:00
2026-03-21T09:00:05+00:00 EXIT: code 1
... (repeats for 6 more hours)
```

**jsspec** (06:00–06:35, last run before auth death): Adds 20+ more proof theorems including `Behaves_deterministic` — programs have unique traces. Total: ~97 Core proof theorems with 0 sorry.

> "PROVED: Behaves_deterministic — programs have unique traces. THIS IS A KEY RESULT"

---

## Hour 18–24: Revival & The Simp Loop Saga (14:00–20:00 UTC)

Tokens refreshed. Agents restart. But jsspec has been adding `simp [step?]` calls to new theorems, and the Lean equation lemma `step?.eq_1` causes an infinite simplification loop. The build breaks.

**jsspec** (13:21–14:21): Runs for an hour but times out (EXIT 124). The simp loop means `lake build VerifiedJS.Core.Semantics` hangs.

**jsspec** (15:00–16:00, 17:00–18:00, 19:00–20:00): Three more timeout runs. Each time jsspec tries to work but the build is broken by its own simp loop.

**supervisor** (20:05): Finally catches up and writes a thorough diagnosis:

> "Build FAIL (57 errors in Core/Semantics.lean stuck_implies_lit). Root cause: jsspec's simp [step?, h] on lines 2173-2213 triggers step?.eq_1 simp loop. Build has been broken since ~14:05 (6 hours)."

Updates the proof chain status table. Notes sorry plateau at 6 for 16+ consecutive runs.

**supervisor** (22:05): Even more detailed analysis. Rewrites jsspec's prompt with the simplest possible fix. Notes:

> "jsspec: DEAD — EXIT 1 in 10 seconds. Not executing prompts. Last meaningful work: 2026-03-21T17:00"

The human manually sorrys the broken theorem to unblock the build.

---

## Hour 24–30: MCP Integration & Recovery (20:00–23:00 UTC)

The human installs the Lean LSP MCP server and fixes it to work for agent users (the `uvx` cache permission issue). Deploys new prompts telling agents to use `lean_multi_attempt` before writing proofs.

**All agents** restarted with MCP connected. Run logs show:
```
"lean-lsp","status":"connected"
```

**wasmspec**: 11 `lean_goal` calls, 5 `lean_diagnostic_messages`, 5 `lean_loogle` — the heaviest MCP user.

**jsspec** (22:24–22:45): Returns to productive work. Adds 6 exact-derivation theorems, fixes lexer whitespace handling per ECMA-262 §11.2/§11.3. Analyzes test262 skip categories.

**proof**: Uses 7 `lean_diagnostic_messages` — checking errors without rebuilding.

---

## Key Metrics Evolution

| Time | Sorries | E2E Pass | E2E Total | Lean LOC | Theorems |
|------|---------|----------|-----------|----------|----------|
| 16:30 (start) | 12 | 8/10 | 10 | 13,000 | ~5 |
| 16:52 | 6 | 13/17 | 17 | 13,100 | ~8 |
| 17:12 | 4 | 17/21 | 21 | 13,300 | ~12 |
| 18:13 | 4 | 25/30 | 30 | 13,500 | ~15 |
| 20:40 | 4 | 40/43 | 43 | 14,000 | ~20 |
| 00:30 | 4 | 74/77 | 77 | 14,100 | ~34 |
| 02:15 | 4 | 102/105 | 105 | 15,000 | ~56 |
| 03:10 | 4 | 120/123 | 123 | 15,500 | ~74 |
| 06:35 | 4 | ~170 | ~173 | 16,000 | ~97 |
| 08:00-14:00 | (auth dead) | — | — | — | — |
| 22:45 | 7 | ~120/203 | 203 | 21,000 | ~100 |

---

## Notable Interactions

### The step? Saga
1. **Hour 0**: proof agent identifies `step?` being `partial def` as the root blocker for 6 sorries
2. **Hour 0.5**: proof agent writes exact fix instructions for jsspec: "Make step? non-partial using termination_by sizeOf s.expr"
3. **Hour 1**: wasmspec tries to fix Flat/ANF step? first, breaks the build
4. **Hour 1.5**: wasmspec fixes it properly — Flat.step? and ANF.step? become non-partial
5. **Hour 4**: jsspec finally makes Core.step? non-partial, unblocking the proof agent
6. **Total time from diagnosis to fix**: ~4 hours

### The Build Break Chain
1. wasmspec breaks ANF/Semantics.lean by removing `partial` without termination proof
2. jsspec can't run e2e tests because the build is broken
3. proof agent can't verify its proofs
4. Human has to remove Duper/Canonical deps to fix the build
5. Later: jsspec introduces simp loop, breaks build for 6+ hours
6. Human has to manually sorry the broken theorem

### wasmspec Unblocks proof
wasmspec makes `valuesFromExprList?` public and adds a bridge lemma `firstNonValueExpr_none_implies_values`. proof agent immediately uses it to prove constructor cases in halt_preservation. This is genuine cross-agent collaboration mediated by code.

### The Discovery of a False Theorem
proof agent discovers that `closureConvert_halt_preservation` is mathematically FALSE for stubbed features (for-in/for-of). This is a real mathematical insight — the compiler produces `.lit .undefined` for unimplemented features, which halts in the target language but steps in the source. The theorem statement needs to be restricted to implemented features.

---

## What Worked

1. **Specialization**: Each agent stayed in its lane. jsspec wrote semantics, wasmspec wrote Wasm specs, proof proved things.
2. **The proof agent's first 2 hours**: Going from 11 to 4 sorries, restructuring proofs with simulation relations, building runtime helpers. Extraordinary productivity.
3. **jsspec's test explosion**: 203 e2e tests covering closures, recursion, bitwise ops, try/catch, typeof, etc.
4. **jsspec's proof theorems**: 97 lemmas about Core semantics with zero sorry — step_deterministic, Behaves_deterministic, totality lemmas for all operators.
5. **Cross-agent unblocking**: wasmspec making definitions public when proof needed them.

## What Didn't Work

1. **Sorry plateau**: The 4 core sorries (step simulation theorems) never got resolved despite 30 hours. They require ~200+ lines of case analysis that the agents keep timing out on.
2. **Build breaks**: Agents broke the build multiple times by modifying shared dependencies (step? partiality, simp loops, git operations on .lake/packages).
3. **Auth token management**: 8 hours lost to expired OAuth tokens. No automatic refresh mechanism.
4. **The supervisor's passivity**: Despite identifying blockers accurately, the supervisor rarely wrote to other agents' prompts to redirect them. It observed and documented but didn't act forcefully enough.
5. **Test262 stagnation**: 2/93 passing for 30+ hours. None of the agents made meaningful progress on conformance suite coverage.
6. **Simp loop recurrence**: jsspec kept re-introducing `simp [step?]` even after being told not to. The equation lemma for step? causes infinite unfolding.
