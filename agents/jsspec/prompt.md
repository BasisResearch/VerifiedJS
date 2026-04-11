# jsspec — FIX closureConvert TO ADD logBuiltin AT INDEX 0

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 15 CC sorries remain. Total: 46.

## P0: FIX closureConvert TO SEED logBuiltin AT INDEX 0 — THEN CLOSE L1519

**THE PROBLEM**: Core.initialState has `funcs := #[logBuiltin]` at index 0. But closureConvert starts from `CCState.empty` (funcs = #[]). So FuncsCorr cannot be proved for the initial state.

**THE FIX** (2 edits):

### Step 1: Add logBuiltin FuncDef in Flat/ClosureConvert.lean

After `CCState.empty` definition (L17), add:

```lean
/-- Flat equivalent of Core's logBuiltin: reserved at function index 0. -/
def logBuiltinFuncDef : FuncDef :=
  { name := "log", params := ["__arg__"], envParam := "__env_log", body := .lit .undefined }
```

### Step 2: Modify closureConvert to seed with logBuiltin

Change L326 from:
```lean
  let st0 := CCState.empty
```
to:
```lean
  let st0 := { CCState.empty with funcs := #[logBuiltinFuncDef] }
```

This shifts user function indices to 1+, but `addFunc` uses `st.funcs.size` so all `.closure` funcIdx values will be correct. `consoleLogIdx = 0` is already special-cased in Flat.step? (L499), so `funcs[0]` is never actually looked up at runtime.

### Step 3: Close L1519

After making the fix, the goal at L1519 becomes:
```
FuncsCorr id #[logBuiltin] t.functions t.functions
```

Where `t.functions[0] = logBuiltinFuncDef`. Now provable:
1. `unfold FuncsCorr`
2. Part (1): ccFuncs ≤ flatFuncs: trivially `t.functions.size ≤ t.functions.size`
3. Part (2): `1 ≤ t.functions.size` — follows from closureConvert producing at least logBuiltinFuncDef
4. For i=0: `fd = logBuiltinFuncDef`, `fd.params = ["__arg__"] = logBuiltin.params` ✓
5. `fd.body = .lit .undefined = (convertExpr (.lit .undefined) ...).fst` — `convertExpr` on `.lit` is identity

You also need to update L1538-1539 in ClosureConvertCorrect.lean which reference `CCState.empty` — change to `{ CCState.empty with funcs := #[logBuiltinFuncDef] }`.

### Step 4: Verify with lean_diagnostic_messages

Check that no new errors appear from the change. The key risk: proofs that assume `closureConvert` starts with empty funcs.

**EXPECTED RESULT**: -1 sorry (L1519 closed).

## P1: ERROR STRUCTURAL MISMATCH (L5152, L5251, L5490) — INVESTIGATE

Run `lean_goal` at each. If they're truly structural (Flat drops .let on error, Core keeps it), document the mismatch. If there's a workaround, close them.

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5333, L5359, L8201, L8204, L8278, L8394: CCStateAgree (6 total)
- L4984, L5933, L6141, L6152: multi-step simulation gap (4 total)
- L6792: semantic mismatch (UNPROVABLE)
- L8044: functionDef (multi-step + FuncsCorr maintenance)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — logBuiltin fix + L1519" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
