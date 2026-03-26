# proof — Close CC step_sim cases

## Build ONLY your module
```
bash scripts/lake_build_concise.sh VerifiedJS.Proofs.ClosureConvertCorrect
```

## Use MCP BEFORE editing
- lean_goal to see state
- lean_multi_attempt to test tactics
- lean_diagnostic_messages for errors

## TASK 1: Close `break` (L1063) and `continue` (L1064)

These are nearly identical. `convertExpr (.break label) = (.break label, st)` and both Core/Flat produce error events with the same label string.

Replace L1063 `| «break» label => sorry` with:

```lean
  | «break» label =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«break» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    -- Flat step: break label => error "break:" ++ label.getD ""
    have hfs : Flat.step? { sf with expr := .«break» label } =
        some (.error ("break:" ++ (label.getD "")),
          { expr := .lit .undefined, env := sf.env, heap := sf.heap,
            trace := sf.trace ++ [.error ("break:" ++ (label.getD ""))],
            funcs := sf.funcs, callStack := sf.callStack }) := by
      simp [Flat.step?]; rfl
    rw [hfs] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    -- Core step: break label => error (match label ...)
    -- Show the label strings match
    have hlabel_eq : (match label with | some s => "break:" ++ s | none => "break:") =
        "break:" ++ label.getD "" := by
      cases label <;> simp [Option.getD]
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("break:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Core.step? sc = some (.error ("break:" ++ label.getD ""), sc')
      have hsc' : sc = { sc with expr := .«break» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; simp [Core.step?, Core.pushTrace, hlabel_eq]
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, Flat.convertValue]⟩
```

Replace L1064 `| «continue» label => sorry` with the SAME pattern but "continue:" instead of "break:":

```lean
  | «continue» label =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«continue» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    have hfs : Flat.step? { sf with expr := .«continue» label } =
        some (.error ("continue:" ++ (label.getD "")),
          { expr := .lit .undefined, env := sf.env, heap := sf.heap,
            trace := sf.trace ++ [.error ("continue:" ++ (label.getD ""))],
            funcs := sf.funcs, callStack := sf.callStack }) := by
      simp [Flat.step?]; rfl
    rw [hfs] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    have hlabel_eq : (match label with | some s => "continue:" ++ s | none => "continue:") =
        "continue:" ++ label.getD "" := by
      cases label <;> simp [Option.getD]
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("continue:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Core.step? sc = some (.error ("continue:" ++ label.getD ""), sc')
      have hsc' : sc = { sc with expr := .«continue» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; simp [Core.step?, Core.pushTrace, hlabel_eq]
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, Flat.convertValue]⟩
```

## TASK 2: Close `labeled` (L1066)

`convertExpr (.labeled label body) = (.labeled label body', st1)` where `(body', st1) = convertExpr body ...`. Both Core and Flat unwrap to body with `.silent`.

```lean
  | labeled label body =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst'⟩ := hconv
    -- sf.expr = .labeled label body' where (body', st1) = convertExpr body ...
    have hsf_eta : sf = { sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).fst } := by
      cases sf; simp_all
    rw [hsf_eta] at hstep
    have hfs : Flat.step? { sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).fst } =
        some (.silent, { expr := (Flat.convertExpr body scope envVar envMap st).fst,
          env := sf.env, heap := sf.heap,
          trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
      simp [Flat.step?]; rfl
    rw [hfs] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State := ⟨body, sc.env, sc.heap,
      sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Core.step? sc = some (.silent, sc')
      have hsc' : sc = { sc with expr := .labeled label body } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; simp [Core.step?, Core.pushTrace]
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · show noCallFrameReturn sc'.expr = true
      simp [sc']; exact hncfr
    · show ExprAddrWF sc'.expr sc'.heap.objects.size
      simp [sc']; exact hexprwf
    · exact ⟨scope, st, (Flat.convertExpr body scope envVar envMap st).snd, by simp [sc']⟩
```

**Note**: The `noCallFrameReturn` and `ExprAddrWF` for `labeled` recurse into `body`, so `hncfr` and `hexprwf` should provide what we need after `simp [noCallFrameReturn]` / `simp [ExprAddrWF]`. If `exact hncfr` doesn't work, try `simp [noCallFrameReturn] at hncfr ⊢; exact hncfr`.

## TASK 3: Close `var` subcase A (non-captured)

The code is in the PREVIOUS prompt and follows `this` exactly. Copy the `var` code block from the `.this` case pattern, substituting `name` for `"this"`.

## What NOT to do
- Do NOT change HeapInj/EnvCorrInj/EnvCorr definitions
- Do NOT change CC_SimRel structure
- Do NOT change any file outside ClosureConvertCorrect.lean
- NEVER break the build — `lean_diagnostic_messages` before committing

## Log progress to agents/proof/log.md
