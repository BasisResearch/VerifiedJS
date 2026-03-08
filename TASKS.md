# VerifiedJS — Task List

## Priority 1 (blocking — end-to-end correctness)
- [ ] Parser milestone: parse ≥95% of JS files selected by `scripts/parse_flagship.sh --full` (current: 86.79% = 1781/2052 on 2026-03-08)
- [ ] Implement Wasm runtime helper stubs (indices 0-15): `call`, `construct`, `getProp`, `setProp`, `getIndex`, `setIndex`, `deleteProp`, `typeof`, `getEnv`, `makeEnv`, `makeClosure`, `objectLit`, `arrayLit`, `throw`, `yield`, `await` — without these, any program with function calls or property access fails in wasmtime with "function index out of bounds"
- [ ] Fix value representation in Wasm lowering: all JS values are currently lowered as i32 (ptr) but numeric operations need proper f64 handling. Need NaN-boxing or tagged pointer scheme.
- [ ] Fix float constant emission: `lowerTrivial` emits ptr constants for numbers but the Wasm emit maps ptr→i32, losing float precision. Numbers like `1.5` become `0`.
- [ ] Handle global variable references in lowering (e.g., `console`, `Math`, `JSON`) — currently fails with "unbound variable"

## Priority 2 (important — completeness)
- [ ] Elaborate: implement class declarations (SPEC §14.6) — currently stubs
- [ ] Elaborate: implement for-in/for-of (SPEC §13.7) — currently stubs
- [ ] Elaborate: implement destructuring (SPEC §13.15.5) — currently stubs
- [ ] Elaborate: implement optional chaining (SPEC §13.3) — currently stubs
- [ ] Core.Interp: implement remaining constructs (currently returns "unimplemented" for many)
- [ ] Make test suite cover more of the parser
- [ ] Make test suite cover core elaboration
- [ ] Make test suite check ANF conversion
- [ ] Make test suite check Wasm lowering

## Priority 3 (proof work)
- [ ] Prove ElaborateCorrect.lean
- [ ] Prove ClosureConvertCorrect.lean
- [ ] Prove ANFConvertCorrect.lean
- [ ] Prove LowerCorrect.lean
- [ ] Prove EmitCorrect.lean
- [ ] Compose EndToEnd.lean

## Priority 4 (runtime)
- [ ] Implement Runtime.Values (NaN-boxing)
- [ ] Implement Runtime.GC (mark-sweep in Wasm)
- [ ] Implement Runtime.Objects (property maps in linear memory)
- [ ] Implement Runtime.Strings (interned UTF-16)
- [ ] Implement Runtime.Regex (DFA/NFA engine)
- [ ] Implement Runtime.Generators (CPS/state machines)

## Priority 5 (testing and validation)
- [ ] Set up Test262 test harness
- [ ] Write unit tests for each IL
- [ ] Write e2e tests (compile + run on wasmtime) — 10 handcrafted tests in tests/e2e/ — TODO(supervisor): validator execution failed (completeness-pass-1); validator execution failed (completeness-pass-2)
- [ ] Set up differential testing against Node.js
- [ ] Flagship: compile Prettier
- [ ] Flagship: compile Babel
- [ ] Flagship: compile tsc

## Priority 6 (quality)
- [ ] Write ARCHITECTURE.md with IL descriptions and TCB boundary
- [ ] Deduplicate utility code across modules
- [ ] Review and update spec citations
- [ ] Multi-file compilation support (currently single-file only; no module resolution, import/export linking)

## Validated Completed (Supervisor)
- [x] Define JS.Source.AST inductive types (full ECMAScript 2020) — VALIDATED 2026-03-08
- [x] Implement JS.Source.Lexer — VALIDATED 2026-03-08
- [x] Implement JS.Source.Parser — VALIDATED 2026-03-08
- [x] Parser milestone: multi-token expression/statement parsing — VALIDATED 2026-03-08
- [x] Define JS.Core.Syntax inductive types — VALIDATED 2026-03-08
- [x] Define JS.Flat.Syntax inductive types — VALIDATED 2026-03-08
- [x] Define JS.ANF.Syntax inductive types — VALIDATED 2026-03-08
- [x] Define Wasm.Syntax (port from WasmCert-Coq) — VALIDATED 2026-03-08
- [x] Implement ANF.Convert (JS.Flat → JS.ANF) — VALIDATED 2026-03-08
- [x] Implement Wasm.Lower (JS.ANF → Wasm.IR) — VALIDATED 2026-03-08
- [x] Define Flat.Semantics small-step LTS — VALIDATED 2026-03-08
- [x] Define ANF.Semantics small-step LTS — VALIDATED 2026-03-08
- [x] Define Wasm.Semantics (port from WasmCert-Coq) — VALIDATED 2026-03-08
- [x] Write Core.Interp reference interpreter — VALIDATED 2026-03-08
- [x] Write Core.Print pretty-printer
- [x] Write Flat.Print pretty-printer
- [x] Write ANF.Print pretty-printer
- [x] Write Wasm.Print WAT printer (all Wasm instructions)
- [x] Write Wasm.IR.Print pretty-printer
- [x] Write Flat.Interp reference interpreter
- [x] Write ANF.Interp reference interpreter
- [x] Write Wasm.IR.Interp reference interpreter
- [x] Implement Core.Elaborate (JS.AST → JS.Core)
- [x] Implement Flat.ClosureConvert (JS.Core → JS.Flat)
- [x] Implement Wasm.Emit (Wasm.IR → Wasm.AST)
- [x] Implement Wasm.Binary (Wasm.AST → .wasm)
- [x] Wire up Driver.lean CLI with full pipeline
- [x] Define JS.Core.Semantics small-step LTS
- [x] End-to-end: Parse → Core → Flat → ANF → Wasm.IR → Wasm.AST → .wasm binary
