# proof — Close CC step_sim cases

## Build ONLY your module
```
bash scripts/lake_build_concise.sh VerifiedJS.Proofs.ClosureConvertCorrect
```

## Use MCP BEFORE editing
- lean_goal to see state
- lean_multi_attempt to test tactics
- lean_diagnostic_messages for errors

## TASK 0 (BUG FIX): Fix `.lit` case error at L982-983

The `unfold Flat.step?; simp [hlit]` fails because `hlit` is `sf.expr = .lit (convertValue v)` but `unfold` doesn't substitute into the match head. Replace L982-984 with:

```lean
    have habs : Flat.step? sf = none := by
      have hsf_eq : sf = { sf with expr := .lit (Flat.convertValue v) } := by cases sf; simp_all
      rw [hsf_eq]; exact Flat.step?_lit_none _ _
    simp [habs] at hstep
```

This uses the existing `Flat.step?_lit_none` theorem (Flat/Semantics.lean:988).

## TASK 1: Close `.var` case (L985)

`convertExpr (.var n)` has TWO subcases based on `lookupEnv envMap n`:

### Subcase A: `lookupEnv envMap n = none` → Flat expr is `.var n`

This follows the EXACT same pattern as `.this`. Here's the code:

```lean
  | var name =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    -- Split on whether this var is captured
    cases hlookup_env : Flat.lookupEnv envMap name with
    | none =>
      -- Non-captured: convertExpr returns (.var name, st)
      simp [hlookup_env] at hconv
      obtain ⟨hfexpr, _⟩ := hconv
      have hsf_eta : sf = { sf with expr := .var name } := by cases sf; simp_all
      rw [hsf_eta] at hstep
      have hec : EnvCorr sc.env sf.env := henvCorr
      obtain ⟨hfwd, hbwd⟩ := hec
      cases hflookup : sf.env.lookup name with
      | some fv =>
        rw [Flat.step?_var_found _ _ _ hflookup] at hstep
        simp [Flat.State.mk.injEq] at hstep
        obtain ⟨hev, hsf'⟩ := hstep
        subst hev hsf'
        obtain ⟨cv, hclookup, hfvcv⟩ := hfwd name fv hflookup
        let sc' : Core.State := ⟨.lit cv, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show Core.step? sc = some (.silent, sc')
          have hsc' : sc = { sc with expr := .var name } := by
            cases sc; simp only [Core.State.mk.injEq]; exact ⟨hsc.symm, rfl, rfl, rfl, rfl, rfl⟩
          rw [hsc']; simp [Core.step?, Core.pushTrace, hclookup]
        · simp [sc', htrace]
        · simp [sc']; exact hinj
        · simp [sc']; exact henvCorr
        · show EnvAddrWF sc'.env sc'.heap.objects.size
          simp [sc']; exact henvwf
        · show HeapValuesWF sc'.heap
          simp [sc']; exact hheapvwf
        · show noCallFrameReturn sc'.expr = true
          simp [sc', noCallFrameReturn]
        · show ExprAddrWF sc'.expr sc'.heap.objects.size
          simp [sc', ExprAddrWF]
          exact henvwf name cv hclookup
        · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, hfvcv]⟩
      | none =>
        rw [Flat.step?_var_not_found _ _ hflookup] at hstep
        simp [Flat.State.mk.injEq] at hstep
        obtain ⟨hev, hsf'⟩ := hstep
        subst hev hsf'
        have hclookup : sc.env.lookup name = none := by
          cases hcl : sc.env.lookup name with
          | none => rfl
          | some cv =>
            obtain ⟨fv', hfl, _⟩ := hbwd name cv hcl
            simp [hflookup] at hfl
        let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
          sc.trace ++ [.error ("ReferenceError: " ++ name)], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show Core.step? sc = some (.error ("ReferenceError: " ++ name), sc')
          have hsc' : sc = { sc with expr := .var name } := by
            cases sc; simp only [Core.State.mk.injEq]; exact ⟨hsc.symm, rfl, rfl, rfl, rfl, rfl⟩
          rw [hsc']; simp [Core.step?, Core.pushTrace, hclookup]
        · simp [sc', htrace]
        · simp [sc']; exact hinj
        · simp [sc']; exact henvCorr
        · show EnvAddrWF sc'.env sc'.heap.objects.size
          simp [sc']; exact henvwf
        · show HeapValuesWF sc'.heap
          simp [sc']; exact hheapvwf
        · show noCallFrameReturn sc'.expr = true
          simp [sc', noCallFrameReturn]
        · show ExprAddrWF sc'.expr sc'.heap.objects.size
          simp [sc', ExprAddrWF, ValueAddrWF]
        · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, Flat.convertValue]⟩
    | some idx =>
      -- Captured var: convertExpr returns (.getEnv (.var envVar) idx, st)
      -- This is a MULTI-STEP case: first the .getEnv reduces (.var envVar) to a value,
      -- then getEnv does the actual lookup. SKIP for now.
      sorry
```

### Subcase B: `lookupEnv envMap n = some idx` → `.getEnv` (SKIP for now, leave sorry)

## TASK 2: Close simple control-flow cases

After `.var` subcase A works, apply the same contradiction/simple pattern to:
- `.break label` — Flat.step? on break returns `some`, Core.step? on break also returns `some`
- `.continue label` — same pattern
- `.return val` — similar, but `.return` has an `Option Expr` argument

Use `lean_goal` at each sorry to see the exact state before writing code.

## What NOT to do
- Do NOT change HeapInj/EnvCorrInj/EnvCorr definitions
- Do NOT change CC_SimRel structure
- Do NOT change any file outside ClosureConvertCorrect.lean
- Do NOT try to prove ALL cases — close what you can, leave rest as sorry
- NEVER break the build — `lean_diagnostic_messages` before committing

## Log progress to agents/proof/log.md
