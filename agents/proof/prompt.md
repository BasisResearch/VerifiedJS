# proof — CRITICAL: Strengthen suffices with CCStateAgree to unblock ALL 6 CCState sorries

## WHY YOU'RE STUCK (and the fix)

The 6 CCState sorries (L1987, L2194, L2283, L2522, L2645, L2917) are ALL blocked by the same root cause:

When a sub-expression steps (e.g., `init` in `let x = init in body`), the IH gives back
`scope', st_a, st_a'` with `(sa.expr, st_a') = convertExpr sc_sub'.expr scope' envVar envMap st_a`.

But the body was converted under `(convertExpr init scope envVar envMap st).snd`, and the
reconverted body uses `(convertExpr sc_sub'.expr scope' envVar envMap st_a).snd = st_a'`.
You need `CCStateAgree (convertExpr init scope envVar envMap st).snd st_a'` to bridge via
`convertExpr_state_determined`, but the current suffices doesn't track this.

## THE FIX: Strengthen the suffices (L1748-1770)

### Step 1: Change the suffices statement

Current (L1748-1766):
```lean
suffices ∀ (n : Nat) (envVar : String) (envMap : Flat.EnvMapping) (injMap : Nat → Nat)
    (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State),
    sc.expr.depth = n → sf.trace = sc.trace →
    HeapInj injMap sc.heap sf.heap → EnvCorrInj injMap sc.env sf.env →
    EnvAddrWF sc.env sc.heap.objects.size →
    HeapValuesWF sc.heap →
    noCallFrameReturn sc.expr = true →
    ExprAddrWF sc.expr sc.heap.objects.size →
    (∃ (scope : List String) (st st' : Flat.CCState),
      (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st) →
    Flat.Step sf ev sf' →
    ∃ (injMap' : Nat → Nat) (sc' : Core.State), Core.Step sc ev sc' ∧ sf'.trace = sc'.trace ∧
      HeapInj injMap' sc'.heap sf'.heap ∧ EnvCorrInj injMap' sc'.env sf'.env ∧
      EnvAddrWF sc'.env sc'.heap.objects.size ∧
      HeapValuesWF sc'.heap ∧
      noCallFrameReturn sc'.expr = true ∧
      ExprAddrWF sc'.expr sc'.heap.objects.size ∧
      (∃ (scope : List String) (st st' : Flat.CCState),
        (sf'.expr, st') = Flat.convertExpr sc'.expr scope envVar envMap st)
```

Change to (move scope/st/st' from existential to universal, add CCStateAgree output):
```lean
suffices ∀ (n : Nat) (envVar : String) (envMap : Flat.EnvMapping) (injMap : Nat → Nat)
    (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State)
    (scope : List String) (st st' : Flat.CCState),
    sc.expr.depth = n → sf.trace = sc.trace →
    HeapInj injMap sc.heap sf.heap → EnvCorrInj injMap sc.env sf.env →
    EnvAddrWF sc.env sc.heap.objects.size →
    HeapValuesWF sc.heap →
    noCallFrameReturn sc.expr = true →
    ExprAddrWF sc.expr sc.heap.objects.size →
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st →
    Flat.Step sf ev sf' →
    ∃ (injMap' : Nat → Nat) (sc' : Core.State), Core.Step sc ev sc' ∧ sf'.trace = sc'.trace ∧
      HeapInj injMap' sc'.heap sf'.heap ∧ EnvCorrInj injMap' sc'.env sf'.env ∧
      EnvAddrWF sc'.env sc'.heap.objects.size ∧
      HeapValuesWF sc'.heap ∧
      noCallFrameReturn sc'.expr = true ∧
      ExprAddrWF sc'.expr sc'.heap.objects.size ∧
      (∃ (st_a st_a' : Flat.CCState),
        (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
        CCStateAgree st st_a ∧ CCStateAgree st' st_a')
```

### Step 2: Update the outer proof (L1767-1770)

```lean
  by
    intro sf sc ev sf' ⟨htrace, ⟨injMap, hinj, henv⟩, hncfr, hexprwf, henvwf, hheapvwf, scope, envVar, envMap, st, st', hconv⟩ hstep
    obtain ⟨injMap', sc', hcstep, htrace', hinj', henv', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', _, _⟩ :=
      this sc.expr.depth envVar envMap injMap sf sc ev sf' scope st st' rfl htrace hinj henv henvwf hheapvwf hncfr hexprwf hconv hstep
    exact ⟨sc', hcstep, htrace', ⟨injMap', hinj', henv'⟩, hncfr', hexprwf', henvwf', hheapvwf', scope, envVar, envMap, st_a, st_a', hconv'.1⟩
```

### Step 3: Update the intro (L1774)

Old: `intro envVar envMap injMap sf sc ev sf' hd htrace hinj henvCorr henvwf hheapvwf hncfr hexprwf ⟨scope, st, st', hconv⟩ ⟨hstep⟩`
New: `intro envVar envMap injMap sf sc ev sf' scope st st' hd htrace hinj henvCorr henvwf hheapvwf hncfr hexprwf hconv ⟨hstep⟩`

(scope/st/st' are now regular arguments, not from an existential. hconv is direct, not in ∃.)

### Step 4: Update each IH call and its output

For the IH call at L1962-1968 (let case), change:
- Input: `⟨scope, st, (Flat.convertExpr init scope envVar envMap st).snd, by simp⟩` → `scope st (Flat.convertExpr init scope envVar envMap st).snd (by simp)`
- Output: add `hAgreeIn, hAgreeOut` to destructor:
  ```lean
  obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ := ...
  ```

### Step 5: Close the CCState sorry (L1987 etc.) using the new invariants

At L1987, the goal is now:
```
∃ st_a st_a', (sf'.expr, st_a') = convertExpr (.let name sc_sub'.expr body) scope envVar envMap st_a ∧
  CCStateAgree st st_a ∧ CCStateAgree st' st_a'
```

Proof:
```lean
· -- Choose st_a from the IH
  refine ⟨st_a, ?_, ?_, ?_, ?_⟩   -- or however the structure works
  -- Unfold convertExpr for .let:
  -- convertExpr (.let name sc_sub'.expr body) scope envVar envMap st_a
  -- = let (e1, s1) = convertExpr sc_sub'.expr scope envVar envMap st_a
  --   let (e2, s2) = convertExpr body (name::scope) envVar envMap s1
  --   (.let name e1 e2, s2)
  -- From hconv': sa.expr = (convertExpr sc_sub'.expr scope envVar envMap st_a).fst
  -- Need body part: use convertExpr_state_determined with hAgreeOut
  have hbody := (convertExpr_state_determined body (name :: scope) envVar envMap
    (Flat.convertExpr init scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2).1
  -- Then show the pair equality using ext/Prod.mk.injEq
  simp only [Flat.convertExpr]  -- unfold the let
  constructor
  · -- Expression equality
    rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from hconv'.1.symm ▸ ... ]
    rw [hbody]
  · constructor
    · exact hAgreeIn
    · -- CCStateAgree for output: use convertExpr_state_determined on body
      exact (convertExpr_state_determined body (name :: scope) envVar envMap
        (Flat.convertExpr init scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2).2
```

The EXACT tactics will depend on the goal state. Use `lean_goal` at each sorry after the refactor.

### Step 6: For non-stepping cases (lit, var value, assign value, etc.)

These cases don't sub-step, so choose `st_a = st, st_a' = st'` and prove `CCStateAgree st st` by `⟨rfl, rfl⟩`.

Example: change the final `⟨scope, st, st', by ...⟩` to `⟨st, st', by ..., ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩`.

## EXECUTION ORDER
1. Make the suffices change (Steps 1-3) FIRST
2. Build to check — expect new errors at each case's final existential
3. Fix non-stepping cases (easy: add `⟨rfl, rfl⟩, ⟨rfl, rfl⟩`)
4. Fix stepping cases using `hAgreeOut` + `convertExpr_state_determined`

## DO NOT TOUCH:
- ANFConvertCorrect, LowerCorrect, Wasm/Semantics
- forIn/forOf at L1132/L1133 (theorem false)
- Value sub-cases at L2530/L2589/L2652

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Use lean_goal + lean_multi_attempt BEFORE every edit.
## Log progress to agents/proof/log.md.
