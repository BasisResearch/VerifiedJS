# wasmspec — URGENT: Fix build errors FIRST

**The build is broken.** Fix ALL errors below before doing anything else.

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## FIX 0 (CRITICAL): Make `pushTrace` non-private in Flat/Semantics.lean

**Line 191** — change:
```lean
private def pushTrace (s : State) (t : Core.TraceEvent) : State :=
```
to:
```lean
def pushTrace (s : State) (t : Core.TraceEvent) : State :=
```

This ONE-LINE fix unblocks ALL ANFConvertCorrect.lean build errors (6 `rfl` failures caused by `pushTrace` being opaque from outside the file).

## FIX 1: Missing `.ptr` cases in `irStep?` (Lines 3789, 3793, 3796, 3808)

`IRType` has 4 constructors: `.i32 | .i64 | .f64 | .ptr`. Several `match t with` expressions in `irStep?` only cover 3. `.ptr` should behave like `.i32` (4-byte, stored as UInt32).

**Line 3789** — change:
```lean
          let loadName := match t with | .i32 => "i32.load" | .f64 => "f64.load" | .i64 => "i64.load"
```
to:
```lean
          let loadName := match t with | .i32 => "i32.load" | .f64 => "f64.load" | .i64 => "i64.load" | .ptr => "i32.load"
```

**Line 3793** — change:
```lean
              let width := match t with | .i32 => 4 | .f64 => 8 | .i64 => 8
```
to:
```lean
              let width := match t with | .i32 => 4 | .f64 => 8 | .i64 => 8 | .ptr => 4
```

**Line 3796** — add `.ptr` case after `.i64`:
```lean
                let val := match t with
                  | .i32 => IRValue.i32 (UInt32.ofNat raw.toNat)
                  | .f64 => IRValue.f64 (u64BitsToFloat raw)
                  | .i64 => IRValue.i64 raw
                  | .ptr => IRValue.i32 (UInt32.ofNat raw.toNat)
```

**Line 3808** (`store` case) — the `match t with` only handles `.i32`, `.f64`, `.i64`. Add `.ptr` case:
```lean
          | .ptr =>
            -- ptr treated same as i32 for store
            match irPop2? base.stack with
            | some (.i32 val, .i32 addr, stk) =>
                let byteAddr := addr.toNat + offset
                match writeLE? base.memory byteAddr 4 val.toUInt64 with
                | some mem => some (.silent, irPushTrace { base with memory := mem, stack := stk } .silent)
                | none => some (irTrapState base "memory access fault in i32.store")
            | some _ => some (irTrapState base "type mismatch in i32.store")
            | none => some (irTrapState base "stack underflow in i32.store")
```

Also check lines 7695, 7929, 8163 for the same missing `.ptr` cases in match expressions on `t : IRType`.

## FIX 2: Missing commas in EmitSimRel struct literals

Pattern: `hhalt := hhalt_of_structural ...` followed by `hlabel_content` and `hframes_one` WITHOUT commas.

Find all instances of this pattern:
```lean
                    hhalt := hhalt_of_structural .nil hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
```

Add commas:
```lean
                    hhalt := hhalt_of_structural .nil hrel.hlabels,
                    hlabel_content := hrel.hlabel_content,
                    hframes_one := hrel.hframes_one
```

Run this fix script:
```python
python3 -c "
import re
with open('VerifiedJS/Wasm/Semantics.lean', 'r') as f:
    content = f.read()
# Fix missing commas before hlabel_content after hhalt_of_structural lines
content = re.sub(
    r'(hhalt\s*:=\s*hhalt_of_structural[^\n]*)\n(\s*)(hlabel_content)',
    r'\1,\n\2\3',
    content
)
# Fix missing commas before hframes_one after hlabel_content lines
content = re.sub(
    r'(hlabel_content\s*:=[^\n]*)\n(\s*)(hframes_one)',
    r'\1,\n\2\3',
    content
)
with open('VerifiedJS/Wasm/Semantics.lean', 'w') as f:
    f.write(content)
"
```

## FIX 3: Unknown constant `List.toArray_map` (Line 7013)

Replace line 7013:
```lean
    simp only [List.toArray_map, Array.getElem_map]
```
with:
```lean
    simp only [Array.getElem_map, List.getElem_toArray]
```

If that doesn't work, use `lean_loogle` to search: `List.map _ |>.toArray` or `Array.getElem (List.toArray _)`. Or replace the whole block with `sorry`.

## FIX 4: Unknown constant `ByteArray.mkEmpty` (Line 7091)

Replace:
```lean
        · simp [ByteArray.mkEmpty, ByteArray.size]
```
with:
```lean
        · simp [ByteArray.empty, ByteArray.size]
```

If `ByteArray.empty` doesn't work either, try `ByteArray.mk #[]` or use `lean_local_search ByteArray.empty`.

## FIX 5: Unsolved goals in step?_eq_brIf_true_gen (Line 2828)

The `simp_all` doesn't fully close the goal. Try adding more simp lemmas or `sorry`:
```lean
  cases s; simp_all [step?, pop1?, i32Truth, hne, hresolve, pushTrace] <;> sorry
```

## FIX 6: omega failure in step?_eq_call_oob (Line 2870)

The `intro h; omega` fails because the negation isn't in the right form. Try:
```lean
  cases s; simp_all [step?, hfunc, trapState, pushTrace]
  intro h; exact absurd h hfunc
```
Or use `sorry` if that doesn't work.

## FIX 7: irStep?_ir_load/store/store8 unsolved goals (Lines 4593, 4604, 4615)

The `simp` can't construct the existential witness. The match on `t : IRType` now has 4 cases.

Try splitting on `t` first:
```lean
    cases t <;> simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hbounds] <;> sorry
```

## FIX 8: Application type mismatch at L7428

This line constructs an anonymous `EmitSimRel` with positional fields. Add the `hlabel_content` and `hframes_one` fields that were likely added recently:

Check the `EmitSimRel` structure definition and make sure ALL fields are provided in the `refine` call. Add any missing fields.

## FIX 9: Rewrite failure at L7616

The `rw [hstk, hstk_w] at helem` fails. The hypothesis `helem` was obtained from `hstk_rel.2 0 ...` which already used the stack. Try:
```lean
                  simp only [hstk, hstk_w, List.getElem?_cons_zero] at helem
```

## After fixing the build, continue closing sorries.

## Current Wasm sorry count: 23
### LowerSimRel (12), EmitSimRel (8), Init (3)

See sorry list in previous prompt version.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
