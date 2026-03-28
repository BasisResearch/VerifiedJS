# wasmspec — FIX ANF SEMANTICS + CLOSE WASM SORRIES

## STATUS: 18 Wasm sorries. ANF semantics have SEMANTIC MISMATCHES blocking 4+ proof-agent sorries. FIX THESE FIRST.

## PRIORITY 0: Fix ANF break/continue/return/throw semantics (-4 ANF sorries unblocked)

**File: `VerifiedJS/ANF/Semantics.lean` (you own this file)**

The ANF semantics produce `.silent` for break/continue/return but Flat produces `.error "break:..."` etc. This mismatch makes 4 sorries in ANFConvertCorrect.lean PERMANENTLY UNPROVABLE. You MUST fix this.

### Fix 1: break (L447-449)
Change from:
```lean
| .«break» label =>
    let s' := pushTrace { s with expr := .trivial .litUndefined } .silent
    some (.silent, s')
```
To:
```lean
| .«break» label =>
    let l := label.getD ""
    let msg := "break:" ++ l
    let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
    some (.error msg, s')
```

### Fix 2: continue (L450-452)
Change from:
```lean
| .«continue» label =>
    let s' := pushTrace { s with expr := .trivial .litUndefined } .silent
    some (.silent, s')
```
To:
```lean
| .«continue» label =>
    let l := label.getD ""
    let msg := "continue:" ++ l
    let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
    some (.error msg, s')
```

### Fix 3: return (L409-421)
Change from `.silent` events to `.error "return:..."` events:
```lean
| .«return» arg =>
    match arg with
    | none =>
        let s' := pushTrace { s with expr := .trivial .litUndefined } (.error "return:undefined")
        some (.error "return:undefined", s')
    | some t =>
        match evalTrivial s.env t with
        | .ok v =>
            let msg := "return:" ++ Core.valueToString v
            let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } (.error msg)
            some (.error msg, s')
        | .error msg =>
            let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
            some (.error msg, s')
```

### Fix 4: throw (L376-383)
Change `.error "throw"` to `.error (Core.valueToString v)` to match Flat:
```lean
| .throw arg =>
    match evalTrivial s.env arg with
    | .ok v =>
        let msg := Core.valueToString v
        let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
        some (.error msg, s')
    | .error msg =>
        let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
        some (.error msg, s')
```

**IMPORTANT**: After making these changes, build:
```
lake env lean VerifiedJS/ANF/Semantics.lean
```
If `Core.valueToString` isn't in scope, check if it's `VerifiedJS.Core.valueToString` or `Flat.valueToString`. The file imports `VerifiedJS.Core.Semantics` so `Core.valueToString` should work.

**After build succeeds**, also check:
```
lake env lean VerifiedJS/Proofs/ANFConvertCorrect.lean 2>&1 | grep -c "error"
```
The sorry cases at L1808-1853 will still be sorry'd but should still build (they don't reference the specific event values).

## PRIORITY 1: Close yield/await in Wasm with `h_supported` hypothesis

The `step_sim` theorem at L6631 does NOT have a supported hypothesis. You need to ADD one.

Change the signature from:
```lean
theorem step_sim (prog : ANF.Program) (irmod : IRModule) :
    ∀ (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State),
    LowerSimRel prog irmod s1 s2 → anfStepMapped s1 = some (t, s1') →
    ∃ s2', irStep? s2 = some (t, s2') ∧ LowerSimRel prog irmod s1' s2'
```
To:
```lean
theorem step_sim (prog : ANF.Program) (irmod : IRModule) :
    ∀ (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State),
    s1.expr.supported = true →
    LowerSimRel prog irmod s1 s2 → anfStepMapped s1 = some (t, s1') →
    ∃ s2', irStep? s2 = some (t, s2') ∧ LowerSimRel prog irmod s1' s2'
```

Wait — `ANF.Expr` doesn't have `.supported`. You need `Core.Expr.supported` but ANF uses `ANF.Expr`. Check if there's an `ANF.Expr.supported` or if you need to define one first. If not, you may need to thread the supported predicate from the Flat/Core level.

If adding supported is too complex, use this alternative approach: prove that yield/await cases are unreachable because `anfStepMapped` on `.yield`/`.await` still produces valid step results. Just close the sorry by following the ANF step? equation:
- yield (none): ANF produces `.silent` → show IR can match
- yield (some): ANF evaluates trivial → show IR can match
- await: same pattern

Check if `lowerExpr` for yield/await produces any IR. If it maps to nothing (stub/unreachable), you may need exfalso via LowerCodeCorr inversion.

## PRIORITY 2: Close break/continue in Wasm (L6813, L6816)

After fixing ANF semantics (Priority 0), break now produces `.error "break:..."`. Check what `lowerExpr` produces for break and follow the pattern.

## DO NOT ATTEMPT
- Compound cases (L6738-6759)
- return-some (L6801)
- call cases (L10776, 10831, 10835)

## FILE: `VerifiedJS/ANF/Semantics.lean` (rw), `VerifiedJS/Wasm/Semantics.lean` (rw)
## LOG to agents/wasmspec/log.md
