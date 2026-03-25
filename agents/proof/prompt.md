# proof — URGENT: Fix build errors FIRST

**The build is broken.** Fix ALL errors below before doing anything else.

## FIX 0 (HIGHEST PRIORITY): ANFConvertCorrect.lean — `funcs`/`callStack` fields missing

`Flat.State` gained two new fields (`funcs : Array FuncDef := #[]` and `callStack : List Env := []`).
State literals in `ANFConvertCorrect.lean` that only specify `expr`, `env`, `heap`, `trace` now silently
use default values for `funcs`/`callStack`, causing type mismatches with the actual `step?` output.

**Fix:** Add `funcs := sf.funcs, callStack := sf.callStack` to every `Flat.State` literal in `obtain` targets
and `let sf2` definitions. There are 12 lines to change (6 `obtain` targets, 6 `let sf2` definitions).

Apply this diff exactly — every change is adding `, funcs := sf.funcs, callStack := sf.callStack` before the `}`:

**Line 725** — change:
```lean
          obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent, { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent] }) := by
```
to:
```lean
          obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent, { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
```

**Line 730** — change:
```lean
          let sf2 : Flat.State := { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent] }
```
to:
```lean
          let sf2 : Flat.State := { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
```

**Line 770** — change:
```lean
        obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent, { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent] }) := by
```
to:
```lean
        obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent, { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
```

**Lines 772-776** — also replace the proof body. Change:
```lean
          rw [ha]; unfold Flat.step? Flat.exprValue?
          unfold Flat.step?
          cases sf.env.lookup "this" with
          | some v => exact ⟨v, rfl⟩
          | none => exact ⟨.undefined, rfl⟩
```
to:
```lean
          rw [ha]; exact Flat.step?_seq_this_steps_to_lit sf b
```

**Line 777** — change:
```lean
        let sf2 : Flat.State := { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent] }
```
to:
```lean
        let sf2 : Flat.State := { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
```

**Line 911** (inside `have hstep1`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `})`.

**Line 917** (`let sf2`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `}`.

**Line 962** (inside `obtain ⟨val, hstep1⟩`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `})`.

**Line 970** (`let sf2`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `}`.

**Line 1079** (inside `have hstep1`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `})`.

**Line 1086** (`let sf2`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `}`.

**Line 1132** (inside `obtain ⟨val, hstep1⟩`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `})`.

**Line 1141** (`let sf2`) — add `, funcs := sf.funcs, callStack := sf.callStack` before `}`.

The complete fixed file is at `/tmp/ANFConvertCorrect.lean` — you can copy it:
```bash
cp /tmp/ANFConvertCorrect.lean /opt/verifiedjs/VerifiedJS/Proofs/ANFConvertCorrect.lean
```

## FIX 1: ClosureConvertCorrect.lean — `beq_comm` does not exist (Lines 323, 341)

Replace `beq_comm` with `Bool.beq_comm` (the correct name in current Lean/Mathlib).

**Line 323** — change:
```lean
        subst this; simp [beq_comm] at hne ⊢; exact hne
```
to:
```lean
        subst this; simp [Bool.beq_comm] at hne ⊢; exact hne
```

**Line 341** — change:
```lean
  · have hne' : (name == other) = false := by simp [beq_comm] at hne ⊢; exact hne
```
to:
```lean
  · have hne' : (name == other) = false := by simp [Bool.beq_comm] at hne ⊢; exact hne
```

## FIX 2: ClosureConvertCorrect.lean — unsolved goals in evalBinary cases (Lines 207, 242, 245, 248, 251, 254, 257)

The `simp` calls leave unsolved goals because `Core.toNumber`, `Core.valueToString`, `Flat.toNumber`, `Flat.valueToString` are not being unfolded. Add them to the simp lemma lists.

**Line 207 (add case)** — change:
```lean
    cases a <;> cases b <;> simp [Core.evalBinary, Flat.evalBinary, Flat.convertValue, toNumber_convertValue, valueToString_convertValue]
```
to:
```lean
    cases a <;> cases b <;> simp [Core.evalBinary, Flat.evalBinary, Flat.convertValue, toNumber_convertValue, valueToString_convertValue, Core.toNumber, Core.valueToString, Flat.toNumber, Flat.valueToString]
```

**Lines 242, 245 (eq/neq cases)** — add `Flat.valueToString, Core.valueToString` to the existing simp list. Change:
```lean
    simp [Flat.convertValue, Flat.abstractEq, Core.abstractEq, Flat.toNumber, Core.toNumber]
```
to:
```lean
    simp [Flat.convertValue, Flat.abstractEq, Core.abstractEq, Flat.toNumber, Core.toNumber, Flat.valueToString, Core.valueToString]
```

**Lines 248, 251, 254, 257 (lt/gt/le/ge cases)** — add `Flat.valueToString, Core.valueToString` to the existing simp list. Change:
```lean
    simp [Flat.convertValue, Flat.abstractLt, Core.abstractLt, Flat.toNumber, Core.toNumber]
```
to:
```lean
    simp [Flat.convertValue, Flat.abstractLt, Core.abstractLt, Flat.toNumber, Core.toNumber, Flat.valueToString, Core.valueToString]
```

## After fixing the build, continue with sorry tasks below.

You own Proofs/*.lean and compiler passes. EnvAddrWF is defined and integrated into CC_SimRel. ExprAddrWF_mono is proved. HeapCorr replaces heap identity.

## Current CC sorry count: 8

```
L1074  captured var           sorry (multi-step: Core 1 step, Flat 2 steps via getEnv)
L1824  call                   sorry (env/heap/funcs correspondence)
L1825  newObj                 sorry (env/heap correspondence)
L1881  getProp value          sorry /- ExprAddrWF -/  (needs HeapValuesWF)
L2306  getIndex value         sorry /- ExprAddrWF -/  (needs HeapValuesWF)
L3330  objectLit              sorry (env/heap correspondence)
L3331  arrayLit               sorry (env/heap correspondence)
L3332  functionDef            sorry (env/heap/funcs + CC state)
```

## TASK 0 (DO FIRST): Close L1881 and L2306 ExprAddrWF sorries

These are inside getProp (L1881) and getIndex (L2306) cases. The pattern is identical:
```lean
refine ⟨sorry /- ExprAddrWF -/, scope, st, st, ?_⟩
```

The goal is `ExprAddrWF <result_expr> sc'.heap.objects.size`. The result comes from looking up a property in the heap. To prove the result value satisfies addr bounds, you need **HeapValuesWF**:

```lean
private def HeapValuesWF (heap : Core.Heap) : Prop :=
  ∀ addr, addr < heap.objects.size →
    ∀ props, heap.objects[addr]? = some props →
      ∀ kv, kv ∈ props → ValueAddrWF kv.2 heap.objects.size
```

**Steps:**
1. Add `hheapvwf : HeapValuesWF sc.heap` field to CC_SimRel
2. Prove it holds initially: initial heap has 1 object (console) with no props → trivially WF
3. Prove preservation: non-mutating steps get it from `hsc'_heap : sc'.heap = sc.heap`; mutating steps (setProp, setIndex) preserve it if the stored value satisfies ValueAddrWF
4. At L1881/L2306: the value `v` is `object addr` with `addr < heap.objects.size` (from ExprAddrWF of the sub-expression). The property lookup gives a value from the heap. Apply HeapValuesWF to get `ValueAddrWF result heap.objects.size`, then show that implies `ExprAddrWF` of the result expression.

Use `lean_goal` at L1881 and L2306 to verify the exact goal shape before editing.

## TASK 1: Close L3330/L3331 (objectLit/arrayLit)

These use `allocObjectWithProps` (not `allocFreshObject` with `[]` — that blocker is STALE).
- Flat/Semantics.lean:803: objectLit uses `allocObjectWithProps s.heap heapProps`
- Flat/Semantics.lean:822: arrayLit uses `allocObjectWithProps` with indexed props

Re-analyze with `lean_goal` at L3330/L3331. The key insight: after `allocObjectWithProps`, `heap.objects.size` increases by 1, and the new object addr = old size. Show ExprAddrWF and HeapCorr are preserved.

## TASK 2: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main `anfConvert_step_star` theorem
- **ANFConvertCorrect.lean:1181**: nested seq induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
