# proof — HeapInj Phase 1: Definitions + Lemmas

## Build ONLY your module
```
bash scripts/lake_build_concise.sh VerifiedJS.Proofs.ClosureConvertCorrect
```

## Use MCP BEFORE editing
- lean_goal to see state
- lean_multi_attempt to test tactics
- lean_diagnostic_messages for errors

## TASK: Add HeapInj infrastructure (DO NOT change CC_SimRel yet)

ALL 6 real CC sorries are blocked because Flat's `makeEnv` allocates env objects on the shared heap. After any `functionDef` with captures, Flat heap has extra objects, so:
1. `HeapCorr_alloc_both` requires `ch.objects.size = fh.objects.size` — FAILS
2. `convertValue (.object addr) = .object addr` — but Flat allocates at a different addr
3. `convertValue (.function idx) = .closure idx 0` — but actual env ptr ≠ 0

Add these definitions AFTER `HeapCorr_alloc_right` (around line 617), BEFORE `ValueAddrWF`:

```lean
/-- Value correspondence modulo heap address injection.
    Maps Core.Value to Flat.Value allowing different heap addresses. -/
private def convertValueInj (f : Nat → Nat) : Core.Value → Flat.Value
  | .object addr => .object (f addr)
  | .function idx => .closure idx 0  -- env ptr filled separately
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s

/-- Value correspondence: Flat value equals Core value mapped through injection,
    with relaxed closure env ptr (any envPtr accepted for .function/.closure). -/
private def ValueCorr (f : Nat → Nat) : Core.Value → Flat.Value → Prop
  | .object a, .object b => b = f a
  | .function idx, .closure fIdx _ => idx = fIdx
  | .null, .null => True
  | .undefined, .undefined => True
  | .bool a, .bool b => a = b
  | .number a, .number b => a = b
  | .string a, .string b => a = b
  | _, _ => False

/-- ValueCorr implies same "shape" — non-object/function values are literally equal. -/
private theorem ValueCorr_of_convertValue (cv : Core.Value) :
    ValueCorr id cv (Flat.convertValue cv) := by
  cases cv <;> simp [ValueCorr, Flat.convertValue, id]

/-- Memory injection: maps Core heap addresses to Flat heap addresses.
    Core objects at addr a appear at addr f(a) in Flat heap with matching properties. -/
private structure HeapInj (ch fh : Core.Heap) where
  f : Nat → Nat
  inj : ∀ a b, a < ch.objects.size → b < ch.objects.size → f a = f b → a = b
  valid : ∀ a, a < ch.objects.size → f a < fh.objects.size
  preserves : ∀ a, a < ch.objects.size → ch.objects[a]? = fh.objects[f a]?

/-- Identity injection for equal-prefix heaps (subsumes HeapCorr). -/
private theorem HeapInj_of_HeapCorr {ch fh : Core.Heap} (hc : HeapCorr ch fh) :
    HeapInj ch fh where
  f := id
  inj := fun _ _ _ _ h => h
  valid := fun a ha => Nat.lt_of_lt_of_le ha hc.1
  preserves := fun a ha => hc.2 a ha

/-- Injection identity: both heaps are the same. -/
private theorem HeapInj_refl (h : Core.Heap) : HeapInj h h where
  f := id
  inj := fun _ _ _ _ h => h
  valid := fun _ h => h
  preserves := fun _ _ => rfl

/-- Both heaps push same-shaped object: injection extends with f(new_core) = new_flat. -/
private theorem HeapInj_alloc_both {ch fh : Core.Heap}
    (hinj : HeapInj ch fh) (cp fp : List (Core.PropName × Core.Value))
    (hprops : cp.map Prod.fst = fp.map Prod.fst)  -- same keys
    -- NOTE: values in fp should correspond to values in cp via hinj.f
    -- We can add this constraint if needed
    :
    ∃ (hinj' : HeapInj
      { objects := ch.objects.push cp, nextAddr := ch.nextAddr + 1 }
      { objects := fh.objects.push fp, nextAddr := fh.nextAddr + 1 }),
    (∀ a, a < ch.objects.size → hinj'.f a = hinj.f a) ∧
    hinj'.f ch.objects.size = fh.objects.size := by
  sorry

/-- Only Flat heap grows (env object from makeEnv): injection unchanged. -/
private theorem HeapInj_alloc_right {ch fh : Core.Heap}
    (hinj : HeapInj ch fh) (fp : List (Core.PropName × Core.Value)) :
    ∃ (hinj' : HeapInj ch { objects := fh.objects.push fp, nextAddr := fh.nextAddr + 1 }),
    ∀ a, a < ch.objects.size → hinj'.f a = hinj.f a := by
  sorry

/-- Env correspondence modulo injection. -/
private def EnvCorrInj (f : Nat → Nat) (cenv : Core.Env) (fenv : Flat.Env) : Prop :=
  (∀ name fv, fenv.lookup name = some fv →
    ∃ cv, cenv.lookup name = some cv ∧ ValueCorr f cv fv) ∧
  (∀ name cv, cenv.lookup name = some cv →
    ∃ fv, fenv.lookup name = some fv ∧ ValueCorr f cv fv)

/-- EnvCorrInj with id reduces to (almost) EnvCorr. -/
private theorem EnvCorrInj_of_EnvCorr {cenv : Core.Env} {fenv : Flat.Env}
    (h : EnvCorr cenv fenv) : EnvCorrInj id cenv fenv := by
  constructor
  · intro name fv hf
    obtain ⟨cv, hc, hrfl⟩ := h.1 name fv hf
    exact ⟨cv, hc, by subst hrfl; exact ValueCorr_of_convertValue cv⟩
  · intro name cv hc
    obtain ⟨fv, hf, hrfl⟩ := h.2 name cv hc
    exact ⟨fv, hf, by subst hrfl; exact ValueCorr_of_convertValue cv⟩
```

This is Phase 1. It adds definitions WITHOUT changing CC_SimRel or breaking any existing proofs. The 2 sorry lemmas (HeapInj_alloc_both, HeapInj_alloc_right) are construction proofs — build the new injection explicitly.

### Proof sketch for HeapInj_alloc_right
```lean
  refine ⟨⟨hinj.f, ?_, ?_, ?_⟩, fun a ha => rfl⟩
  · exact hinj.inj
  · intro a ha
    have := hinj.valid a ha
    simp [Array.size_push]; omega
  · intro a ha
    have hlt : hinj.f a < fh.objects.size := hinj.valid a ha
    simp [Array.getElem?_push, show ¬(hinj.f a = fh.objects.size) from by omega]
    exact hinj.preserves a ha
```

### Proof sketch for HeapInj_alloc_both
```lean
  -- Define f' : extend f to map ch.objects.size → fh.objects.size
  let f' : Nat → Nat := fun a =>
    if a = ch.objects.size then fh.objects.size
    else if h : a < ch.objects.size then hinj.f a
    else 0  -- unreachable for valid addresses
  refine ⟨⟨f', ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- injectivity: use hinj.inj for old addrs, new addr maps uniquely
    sorry
  · -- validity: old addrs via hinj.valid + push grows, new addr = fh.objects.size < size+1
    sorry
  · -- preserves: old addrs via hinj.preserves + push doesn't affect, new addr via push
    sorry
  · -- old addrs preserved
    intro a ha; simp [f', show ¬(a = ch.objects.size) from by omega, ha]
  · -- new addr
    simp [f']
```

After this compiles, log your progress. Phase 2 (changing CC_SimRel) will come in a later prompt.

## Log progress to agents/proof/log.md
