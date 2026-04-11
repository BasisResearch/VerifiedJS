# jsspec — RELAX CC_SimRel FOR ERROR STATES (closes 3 sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 15 CC sorries remain. Total: 46.
- L1519: CLOSED (FuncsCorr init — nice work!)
- All 15 remaining are architecturally blocked
- CCStateAgree: 6 (L5344, L5370, L8212, L8215, L8289, L8405)
- Multi-step: 4 (L4995, L5944, L6152, L6163)
- Error structural: 3 (L5163, L5262, L5501)
- Unprovable: 1 (L6803)
- functionDef: 1 (L8055)

## P0: FIX ERROR STRUCTURAL MISMATCH (L5163, L5262, L5501) — 3 sorries

### THE PROBLEM
When Flat.step? processes a compound expr (.let, .assign, .seq) and the sub-expression steps to an error, Flat DROPS the wrapper: `sf'.expr = error_result`. But Core.step? KEEPS the wrapper: `sc'.expr = .let name error_result body`.

CC_SimRel (L1503) requires:
```
∃ (scope envVar envMap st st'), (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st
```

After error: `convertExpr (.let name error body) = .let name (convertExpr error ...) (convertExpr body ...)`, which is `.let ...`, but `sf'.expr` has NO `.let`. Mismatch.

### THE FIX: Add error disjunct to CC_SimRel

Modify CC_SimRel (L1491-1504) to add an error alternative for the expression correspondence:

```lean
private def CC_SimRel (_s : Core.Program) (t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  (∃ injMap, HeapInj injMap sc.heap sf.heap ∧ EnvCorrInj injMap sc.env sf.env ∧
    FuncsCorr injMap sc.funcs sf.funcs t.functions) ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧
  EnvAddrWF sc.env sc.heap.objects.size ∧
  HeapValuesWF sc.heap ∧
  sc.heap.nextAddr = sc.heap.objects.size ∧
  sc.expr.supported = true ∧
  (∀ (i : Nat) (fd : Core.FuncClosure), sc.funcs[i]? = some fd → fd.body.supported = true) ∧
  ((∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st) ∨
   -- NEW: error disjunct — when Core expr wraps an error sub-expression,
   -- Flat may have already unwrapped to just the error
   (∃ msg, sf.expr = .lit (.string msg) ∧ Core.exprHasErrorInHead sc.expr = true))
```

You'll need to:
1. Define `Core.exprHasErrorInHead` — checks if the expr is `.error msg` or wraps one in `.let`/`.assign`/`.seq` head position
2. Modify CC_SimRel to use the `∨` disjunct
3. Fix all existing proof sites that destruct the `∃ scope envVar envMap st st'` — add `| Or.inl ⟨scope, ...⟩ =>` and `| Or.inr ⟨msg, ...⟩ =>`
4. For the error disjunct, most cases are contradictions (error state means ANF.step? produces error too, no simulation needed)

### STEP-BY-STEP PLAN

**Step 1**: Define `exprHasErrorInHead` in ClosureConvertCorrect.lean (local defn):
```lean
private def exprHasErrorInHead : Core.Expr → Bool
  | .error _ => true
  | .let _ init _ => exprHasErrorInHead init
  | .assign _ init => exprHasErrorInHead init
  | .seq a _ => exprHasErrorInHead a
  | _ => false
```

**Step 2**: Modify CC_SimRel to add the error disjunct (change last conjunct from `∃ ...` to `(∃ ...) ∨ (∃ msg, ...)`).

**Step 3**: Fix closureConvert_init_related (L1511) — the initial state satisfies the left disjunct (Or.inl).

**Step 4**: Fix closureConvert_step_simulation — at the suffices (L4911), the IH now gives a disjunction. In most cases, the error disjunct from the IH leads to contradictions (Core can't step an already-terminated error). For the 3 error sorries (L5163, L5262, L5501), prove the RIGHT disjunct.

**EXPECTED BLAST RADIUS**: Moderate. Every site that destructs the expression correspondence needs a case split. But the error disjunct should be quickly dismissable in most cases (Core.step? on an error-headed expr produces error, not a normal step).

**EXPECTED RESULT**: -3 sorries (L5163, L5262, L5501 closed). Possibly more if error propagation helps elsewhere.

### RISK MITIGATION
Before modifying CC_SimRel, make a backup:
```bash
cp VerifiedJS/Proofs/ClosureConvertCorrect.lean /tmp/CC_backup_$(date +%s).lean
```

After each step, check with `lean_diagnostic_messages` that you haven't increased error count beyond what's expected.

## SKIP (DO NOT ATTEMPT):
- CCStateAgree (6): needs fundamental refactor
- Multi-step (4): needs stuttering simulation infrastructure
- L6803: semantic mismatch, UNPROVABLE
- L8055: functionDef, multi-step + complex

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CC_SimRel error disjunct" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
