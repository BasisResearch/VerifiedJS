# proof — Close ANF compound sorries via Flat.step? error propagation

## RULES
- Edit: ANFConvertCorrect.lean AND Flat/Semantics.lean
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. ~3.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY
- wasmspec works on L12288-12318 (return/yield/structural) and L16418-16439 (tryCatch)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own Flat/Semantics.lean + compound sorries (L11765, L11916, L11922, L12093, L12099, L12251, L12257)

## STATUS: 66 sorries total. You have been analyzing for days without making code changes. STOP ANALYZING. START EDITING.

## ===== P0: CHANGE Flat.step? NOW =====

**File**: `VerifiedJS/Flat/Semantics.lean`, lines 382-392

**Current code** (L382-392):
```lean
  | .seq a b =>
      match exprValue? a with
      | some _ =>
          let s' := pushTrace { s with expr := b } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := a } with
          | some (t, sa) =>
              let s' := pushTrace { s with expr := .seq sa.expr b, env := sa.env, heap := sa.heap } t
              some (t, s')
          | none => none
```

**REPLACE WITH** (exact code — copy-paste this):
```lean
  | .seq a b =>
      match exprValue? a with
      | some _ =>
          let s' := pushTrace { s with expr := b } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := a } with
          | some (t, sa) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .seq sa.expr b, env := sa.env, heap := sa.heap } t
                  some (t, s')
          | none => none
```

**WHY**: When inner expression `a` produces an error event (throw/break/continue/return), the current code wraps in `.seq sa.expr b` and then `b` executes (dead code!). The fix propagates the error directly. This unblocks 7+ compound sorries.

## ===== P1: FIX BROKEN THEOREMS =====

After changing step?, these will break:

### 1. `Flat_step?_seq_step` in ClosureConvertCorrect.lean L2204-2211
**WAIT** — jsspec owns this file. DO NOT edit it. Instead, tell ME (log it) that jsspec needs to fix this theorem by adding hypothesis `(hne : ∀ msg, t ≠ .error msg)`.

### 2. Theorems in Flat/Semantics.lean that use `simp [step?]` for seq cases
Run `lean_diagnostic_messages` on Flat/Semantics.lean after the change. Fix broken proofs ONE AT A TIME.

### 3. Theorems in ANFConvertCorrect.lean that use `simp [Flat.step?]`
Run `lean_diagnostic_messages` on ANFConvertCorrect.lean. Most will still work because they deal with non-seq cases. Fix any that break.

## ===== P2: ALSO CHANGE .let and .assign cases =====

**ONLY after P0+P1 are stable.** Apply the same error-propagation pattern to:

### `.let name init body` (L348-358):
```lean
  | .«let» name init body =>
      match exprValue? init with
      | some v =>
          let s' := pushTrace { s with expr := body, env := s.env.extend name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := init } with
          | some (t, si) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .«let» name si.expr body, env := si.env, heap := si.heap } t
                  some (t, s')
          | none => none
```

### `.assign name rhs` (L359-369) — same pattern for the none branch.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
2. Edit Flat/Semantics.lean L382-392 with the EXACT code above
3. Run `lean_diagnostic_messages` on Flat/Semantics.lean (filter errors only)
4. Fix each broken proof
5. Run `lean_diagnostic_messages` on ANFConvertCorrect.lean (filter errors only)
6. Fix each broken proof
7. Check compound sorry goals (L11765, L11922, L12099, L12257) — are they now provable?
8. Log what jsspec needs to fix in CC
9. **LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
