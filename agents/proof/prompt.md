# proof — WRITE hasBreakInHead_break_steps (MIRROR hasReturnInHead_return_steps)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE lemma, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T10:30
- ANF: 32 sorries. CC: 15 (jsspec). Total: 47.
- **trivialChain (L10183-L10554) CONFIRMED BLOCKED** — do NOT attempt.
- **LSP times out past ~L10000** in the 18K-line ANFConvertCorrect.lean.
- **Your target**: Write `hasBreakInHead_break_steps` near L5400 (in LSP range).

## ⚠️ DO NOT WORK ON:
- L10183-L10554 (trivialChain — BLOCKED, confirmed 3x)
- L12969-L14177 (wasmspec-owned)
- L14267-L14279 (while — BLOCKED)
- L15004-L15044 (if — BLOCKED)
- L15885-L15906 (tryCatch — BLOCKED)
- L17233, L17244 (noCallFrameReturn/body_sim — BLOCKED)

## P0: hasBreakInHead_break_steps — FOLLOW THE hasReturnInHead_return_steps PATTERN

The sorries at L17463 (break) and L17534 (continue) need error propagation through compound constructors. The EXACT SAME pattern was already implemented for HasReturnInHead at L13346 (`hasReturnInHead_return_steps`). You need to mirror it for HasBreakInHead.

### Step 1: Study the existing pattern

Read L13346-L13600 to understand `hasReturnInHead_return_steps`. Key structure:
- Induction on depth `d`
- For each HasReturnInHead constructor, shows Steps from the expression to an error event
- Uses `Steps_compound_error_lift` (L13135) for compound cases
- Base cases: direct return → error event. Compound cases: IH on sub-expression, then lift.

### Step 2: Check what already exists for break

Use `lean_local_search "HasBreakInHead"` and look at the grep results:
- `HasBreakInHead` inductive at L4463
- `HasBreakInHeadList` at L4498
- `HasBreakInHeadProps` at L4503
- `normalizeExpr_break_implies_hasBreakInHead` at L4906

What's MISSING: a `hasBreakInHead_break_steps` theorem (analogous to `hasReturnInHead_return_steps`).

### Step 3: Write hasBreakInHead_break_steps

Place near L5400 (after the existing break infrastructure, within LSP range).

```lean
/-- Expressions with HasBreakInHead eventually reach a break error event through Flat.Steps.
    Mirrors hasReturnInHead_return_steps. -/
private theorem hasBreakInHead_break_steps
    (d : Nat) :
    ∀ (e : Flat.Expr),
    e.depth ≤ d →
    HasBreakInHead e label →
    ∀ (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
      (funcs : Array Flat.FuncDef) (cs : List Flat.Env),
    ExprWellFormed e env →
    NoNestedAbrupt e →
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs sf' ∧
      sf'.expr = .lit .undefined ∧ sf'.env = env ∧ sf'.heap = heap ∧
      sf'.trace = trace ++ evs ∧
      observableTrace evs = observableTrace [.error ("break:" ++ (label.getD ""))] := by
  sorry -- fill cases below
```

### Step 4: Fill base case

```lean
  intro d; induction d with
  | zero =>
    intro e hd hbreak
    cases hbreak with
    | break_direct =>
      intro env heap trace funcs cs _ _
      refine ⟨[.error ("break:" ++ (label.getD ""))], _,
        .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _),
        rfl, rfl, rfl, rfl, rfl⟩
    | _ => simp [Flat.Expr.depth] at hd; omega
```

### Step 5: Fill compound cases (succ d)

Follow EXACTLY the same pattern as `hasReturnInHead_return_steps` L13367+:
- `| succ d ih =>`
- Match on HasBreakInHead constructors
- break_direct: same as zero case
- Absurd cases (throw_arg, return_some_arg, yield_some_arg, await_arg): `exfalso` via NoNestedAbrupt
- Compound cases: IH on sub-expression, then lift via `Steps_compound_error_lift`

**KEY**: The compound lifting works because `Steps_compound_error_lift` is generic — it takes any wrap function. The same infrastructure serves break, continue, and return.

### Step 6: Write hasContinueInHead_continue_steps

Same structure, replacing `HasBreakInHead` → `HasContinueInHead`, `"break:"` → `"continue:"`.

### Step 7: Verify with lean_diagnostic_messages

After each theorem, check for errors. Even if the body is `sorry`, the TYPE SIGNATURE must compile.

## IMPORTANT: Even sorry'd helpers are valuable

If the full proof of hasBreakInHead_break_steps is too complex, writing the TYPE SIGNATURE + sorry body is still valuable. It structures what L17463/L17534 need, and someone can fill the proof later when LSP allows it.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — hasBreakInHead_break_steps" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
