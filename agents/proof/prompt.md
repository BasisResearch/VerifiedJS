# proof — RESTRUCTURE aux lemmas to multi-step, then close expression cases

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.

## !! CRITICAL BUG FROM LAST RUN !!
Your previous session got PERMANENTLY STUCK in `while pgrep -x lake > /dev/null` because
3 `lake serve` processes run permanently (they are LSP servers, not builds).
**THIS KILLED YOUR ENTIRE SESSION — 5+ HOURS WASTED.**

### ABSOLUTE RULES FOR PROCESS WAITING:
1. **NEVER use `while` loops** — not for pgrep, not for anything
2. **NEVER use `until` loops** — same problem
3. `lake serve` processes are PERMANENT. `pgrep -x lake` will ALWAYS return 0.
4. To check if a BUILD is running: `pgrep -f "lake build"` (NOT `pgrep -x lake`)
5. If a build IS running: just SKIP and do something else. Do NOT wait.
6. If you need to build: just run the build command directly. If another build is running, yours will fail — that's fine, try again later.

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## STATE (01:05): 58 sorries, build PASSES

### Sorry breakdown:
- **40 hasBreak/hasContinue aux** (L3954-4030 + L4085-4161): fundamentally unprovable as stated
- **7 depth-induction** (L3825-3923): normalizeExpr_labeled_step_sim
- **2 makeEnv/objectLit/arrayLit** (L4036, L4167): inside aux lemmas
- **1 compound flat_arg** (L4336)
- **1 HasThrowInHead non-direct** (L4339)
- **7 expression-case** (L4370-4509): throw/return/await/yield/let/seq/if+tryCatch

## PRIORITY 1: RESTRUCTURE hasBreakInHead/hasContinueInHead to multi-step

The 40 sorries in `hasBreakInHead_step?_error_aux` and `hasContinueInHead_step?_error_aux`
are FUNDAMENTALLY UNPROVABLE because the conclusion claims single-step (`Flat.step?`) produces
the error directly, but step? wraps sub-results in the parent context for compound cases.

### APPROACH: Replace single-step aux with multi-step (Steps) theorem

**Step 1**: Delete `hasBreakInHead_step?_error_aux` entirely (~L3927-4036).
**Step 2**: Delete `hasContinueInHead_step?_error_aux` entirely (~L4058-4167).

**Step 3**: Rewrite `hasBreakInHead_flat_error_steps` (~L4041) using STRUCTURAL
INDUCTION on `h : HasBreakInHead e label`. The key insight: each constructor of
HasBreakInHead says "break is in position X" — for the first-evaluation-position cases,
Flat.step? takes one step INTO the sub-expression context, then recursively the inner
break produces error steps. For non-first-position cases, the earlier sub-expression
must evaluate first (multiple steps), THEN the break sub-expression produces error steps.

```lean
private theorem hasBreakInHead_flat_error_steps
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label)
    (sf : Flat.State) (hsf : sf.expr = e) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      observableTrace evs = observableTrace [.error ("break:" ++ label.getD "")] := by
  induction h generalizing sf with
  | break_direct =>
    subst hsf; exact ⟨_, [_], .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _), rfl⟩
  | seq_left hsub ih =>
    subst hsf
    -- Flat.step? {expr := .seq a b} where a is non-value steps INTO a
    -- producing {expr := .seq a' b}. Then ih gives multi-step from a' to error.
    -- Need: Flat.Steps_seq_left_ctx or similar lifting lemma
    sorry -- Use lean_goal here to see exact type, then construct the witness
  -- ... each first-position case follows the same pattern:
  -- 1. step? wraps into context → one step
  -- 2. ih gives multi-step inner → error
  -- 3. Compose with Steps.trans
```

CRITICAL: Check if `Flat.Steps_seq_ctx` or similar context-lifting lemmas exist:
```
lean_local_search "Steps_seq"
lean_local_search "Steps_ctx"
lean_local_search "Flat.Steps"
```
If they don't exist, you need to prove them first. Each says:
"If Flat.Steps {s with expr := e} evs {s' with expr := e'}, then
 Flat.Steps {s with expr := .seq e b} evs {s' with expr := .seq e' b}"

**Step 4**: Same restructuring for `hasContinueInHead_flat_error_steps`.

**Step 5**: Fix callers of the deleted aux theorems. The callers
(`hasBreakInHead_flat_error_steps` itself was the main caller) should now use the
multi-step version directly.

**Step 6**: Build and verify. Target: 58 → 16 sorries (the 42 aux + 2 inner).

## PRIORITY 2: Close 7 expression-case sorries (if time)

At ~L4370-4509 after the restructuring (line numbers will shift):
- throw, return, await, yield, let, seq, if+tryCatch

For each: `lean_goal` → `lean_multi_attempt` with:
```
["simp_all", "exact ⟨_, _, rfl, rfl⟩", "constructor <;> simp_all", "aesop"]
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec own this
- Flat/Semantics.lean — jsspec modified this

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
