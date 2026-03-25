# proof — URGENT: Fix build errors FIRST

**The build is broken.** Fix ALL errors below before doing anything else.

## FIX 0 (HIGHEST PRIORITY): ClosureConvertCorrect.lean — build errors

### Fix 0a: `beq_comm` does not exist (Lines 323, 341)

The issue: after `subst this`, goal is `(name == other) = false` but hypothesis is `hne : (other == name) = false`. VarName = String.

**Line 323** — replace:
```lean
        subst this; simp [beq_comm] at hne ⊢; exact hne
```
with:
```lean
        subst this; rwa [show (name == other) = (other == name) from by simp [beq_iff_eq, eq_comm]]
```

**Line 341** — replace:
```lean
  · have hne' : (name == other) = false := by simp [beq_comm] at hne ⊢; exact hne
```
with:
```lean
  · have hne' : (name == other) = false := by rwa [show (name == other) = (other == name) from by simp [beq_iff_eq, eq_comm]]
```

If `beq_iff_eq` doesn't work, try `BEq.beq_iff_eq` or this fallback:
```lean
        subst this
        have : (name == other) = (other == name) := by
          cases h1 : (name == other) <;> cases h2 : (other == name) <;> simp_all [beq_iff_eq]
        rw [this]; exact hne
```

### Fix 0b: evalBinary unsolved goals (Lines 207, 242, 245, 248, 251, 254, 257)

Add `<;> sorry` at the end of each line that has unsolved goals from `simp`:

**Line 207** (add case):
```lean
    cases a <;> cases b <;> simp [Core.evalBinary, Flat.evalBinary, Flat.convertValue, toNumber_convertValue, valueToString_convertValue] <;> sorry
```

**Lines 242, 245** (eq/neq): append `<;> sorry` after the simp:
```lean
    congr 1; cases a <;> cases b <;> simp [...] <;> sorry
```

**Lines 248, 251, 254, 257** (lt/gt/le/ge): same pattern — append `<;> sorry`.

### Fix 0c: simp no progress at L459 (functionDef case in convertExpr_scope_irrelevant)

Replace line 459:
```lean
    simp only [Flat.convertExpr]
```
with:
```lean
    unfold Flat.convertExpr; rfl
```
If `rfl` doesn't close it, try `simp` or `sorry`.

### Fix 0d: simp timeout at L510 (decreasing_by in convertPropList_scope_irrelevant)

Replace line 510:
```lean
  decreasing_by all_goals simp_all <;> omega
```
with:
```lean
  decreasing_by all_goals (simp (config := { decide := false }) [sizeOf, Prod._sizeOf_inst]; omega)
```
If that still times out, use:
```lean
  decreasing_by all_goals sorry
```

### Fix 0e: ExprAddrWF_mono termination at L655

Add after line 690 (after the last `| .await` case):
```lean
  termination_by e => sizeOf e
  decreasing_by all_goals simp_all [sizeOf] <;> omega
```

### Fix 0f: convertExpr_not_value metavariables at L788-793

Replace line 793:
```lean
  all_goals (first | rfl | (try split) <;> simp [Flat.exprValue?])
```
with:
```lean
  all_goals (first | rfl | sorry)
```

### Fix 0g: `set` unknown tactic at L1279

This is likely a cascading error from L788. Once Fix 0f compiles, check if this resolves. If not, add `import Mathlib.Tactic.Set` at the top, or replace `set x := ... with hdef` with `let x := ...; have hdef : x = ... := rfl`.

## FIX 1: ANFConvertCorrect.lean — `rfl` failures from private `pushTrace`

**Root cause**: `Flat.pushTrace` is `private` in Flat/Semantics.lean. After unfolding `step?`, the goal contains `pushTrace` which can't be reduced from outside the file, so `rfl` fails.

**Wait for wasmspec to make pushTrace non-private.** Once `pushTrace` is visible, all `rfl`/`exact ⟨v, rfl⟩` failures resolve automatically.

**Meanwhile, use the explicit step lemmas that already exist:**

**Line 729** — replace:
```lean
            rw [ha]; unfold Flat.step? Flat.exprValue?
            unfold Flat.step?
            rw [hvar]; exact ⟨v, rfl⟩
```
with:
```lean
            rw [ha]; exact ⟨v, Flat.step?_seq_var_found_explicit sf name v b hvar⟩
```

**Lines 775-776** (this case) — replace:
```lean
          rw [ha]; unfold Flat.step? Flat.exprValue?
          unfold Flat.step?
          cases sf.env.lookup "this" with
          | some v => exact ⟨v, rfl⟩
          | none => exact ⟨.undefined, rfl⟩
```
with:
```lean
          rw [ha]; exact Flat.step?_seq_this_steps_to_lit sf b
```

**Lines 912, 916-917, 1081, 1085-1087** (nested seq cases): these unfold step? multiple times. Replace `rfl` and `exact ⟨_, rfl⟩` with `simp [Flat.step?, Flat.exprValue?, Flat.pushTrace]`. If `pushTrace` is still private, use `sorry` temporarily:

```lean
            rw [hval]; sorry  -- needs pushTrace non-private
```

**Lines 968-969, 1139-1140** (nested this cases): same pattern as 775-776 but nested. Use `sorry` temporarily until pushTrace is non-private.

## After fixing the build, continue with sorry tasks below.

## Current CC sorry count: 9
```
L1074  captured var           sorry (multi-step: Core 1 step, Flat 2 steps via getEnv)
L1836  call                   sorry (env/heap/funcs correspondence)
L1837  newObj                 sorry (env/heap correspondence)
L2156  setProp HeapValuesWF   sorry (set! preserves WF)
L2741  setIndex HeapValuesWF  sorry (set! preserves WF)
L2912  deleteProp HeapValuesWF sorry (filter preserves WF)
L3433  objectLit              sorry (env/heap correspondence)
L3434  arrayLit               sorry (env/heap correspondence)
L3435  functionDef            sorry (env/heap/funcs + CC state)
```

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
