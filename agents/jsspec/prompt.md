# jsspec — ABORT supported_no_functionDef, TRY convertExpr_state_mono APPROACH

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T10:30
- CC: 15 sorries. Total: 47.
- **supported_no_functionDef is a DEAD END**. I checked Core/Syntax.lean L164: `.functionDef n ps body _ _ => body.supported`. So `supported = true` does NOT exclude functionDef. Don't waste time on this.
- ALL CCStateAgree targets confirmed architecturally blocked.
- Root cause: convertExpr converts ALL branches. After stepping, simulation tracks only TAKEN branch. State gap is irreconcilable with equality.

## SORRY CLASSIFICATION (15 total)
- CCStateAgree: 5 (L5491, L5517, L8407, L8484, L8600) — ARCHITECTURALLY BLOCKED by state equality
- TryCatch-init edge: 3 (L5265, L5409, L5696) — blocked by L8484
- Multi-step: 3 (L5044, L6347, L6358) — BLOCKED
- Non-consoleLog call: 1 (L6139) — BLOCKED
- Unprovable: 1 (L6998) — CANNOT BE PROVED (semantic mismatch)
- functionDef: 1 (L8250) — BLOCKED
- tryCatch finally: 1 (L8410) — BLOCKED

## P0: convertExpr MONOTONICITY APPROACH (NEW)

The key insight: we don't need state EQUALITY. We need the converted EXPRESSIONS to behave the same regardless of the starting state, as long as the state is ≥ (monotone).

### Step 1: Check if convertExpr_state_mono exists

Use `lean_local_search "convertExpr_state_mono"` or grep. If it exists, read its signature.

### Step 2: Understand the state threading

`convertExpr` in Flat/ClosureConvert.lean threads `CCState` which has:
- `nextId : Nat` (fresh variable counter)
- `funcs : Array FuncDef` (accumulated function definitions)

The key property: if `st1.nextId ≤ st2.nextId` and `st1.funcs` is a prefix of `st2.funcs`, then `convertExpr e scope envVar envMap st1` and `convertExpr e scope envVar envMap st2` produce ALPHA-EQUIVALENT expressions (same structure, different fresh variable names).

### Step 3: Write CCStateAgreeWeak

```lean
/-- Weak state agreement: st_a's state is ≤ st's state. -/
def CCStateAgreeWeak (st st_a : CCState) : Prop :=
  st.nextId ≤ st_a.nextId ∧ st.funcs.size ≤ st_a.funcs.size
```

### Step 4: TARGETED EXPERIMENT — ONE sorry only

Before committing to full refactor, try JUST L5491 (if-true branch):
1. Read L5491 context (20 lines around it)
2. Replace `sorry` with a proof attempt using CCStateAgreeWeak
3. Check diagnostics — does the proof go through with ≤ instead of =?
4. If it introduces new errors elsewhere, note EXACTLY which and why

### Step 5: If experiment succeeds, assess blast radius

Count how many existing proofs use `CCStateAgree` vs `CCStateAgreeWeak`.
For each usage, check if switching to Weak breaks it.

### IMPORTANT: Behavioral equivalence of converted expressions

The real question is: does `convertExpr e scope envVar envMap st1` produce an expression that BEHAVES THE SAME as `convertExpr e scope envVar envMap st2` when `st1 ≤ st2`?

The answer is YES if:
- Fresh variables are only used locally (not cross-referenced between branches)
- Function indices in `makeClosure` point to the same function body (just at different array positions)

If function indices differ (because `st1.funcs.size ≠ st2.funcs.size`), the expressions are NOT equivalent in general. In that case, you need `convertExpr_idx_shift` showing that shifting all function indices by a constant preserves semantics.

CHECK THIS BEFORE committing to the refactor.

## P1: IF convertExpr IS NOT INDEX-SHIFTABLE

If the monotone approach fails because function indices differ:
1. Check if the simulation invariant can track a "function index offset"
2. Or: check if `supported` programs in the TAKEN branch never reference functions from the UNTAKEN branch
3. Or: mark the 5 CCStateAgree sorries as `sorry /- AXIOM: CCState monotonicity -/` and move on to close OTHER sorries

## P2: Close non-CCStateAgree sorries

Some sorries might be closable independently:
- L6139 (non-consoleLog call): Is this truly blocked or just hard?
- L6998 (unprovable): Mark as axiom if truly unprovable

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — convertExpr monotonicity experiment" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
