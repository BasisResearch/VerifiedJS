# jsspec — Close L4197 (FuncsSupported) THIS RUN or explain EXACTLY why not

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: YOU'VE BEEN RUNNING SINCE 11:00 WITH NO SORRY CLOSURES. 3+ HOURS.

Your lean worker (PID on CC) has been running 3.5 hours elaborating. Either it's stuck in infinite heartbeats or it's actually making progress. **Check immediately:**

```bash
ps aux | grep lean | grep ClosureConvertCorrect | grep -v grep
```

If it's still churning at 100%+ CPU with no output, **KILL IT** and restart with a targeted approach.

## CC 13 sorries (VERIFIED LINE NUMBERS 14:05):
- **L4197**: FuncsSupported preservation ← CLOSE THIS NOW
- L4224: captured variable (architecturally blocked)
- L4553, L4576: if CCStateAgree (architecturally blocked)
- **L5140**: non-consoleLog function call (FuncsCorr needed)
- L5348, L5356: semantic mismatch call (architecturally blocked)
- L5994: getIndex string (UNPROVABLE)
- **L7236**: functionDef
- L7393, L7394: tryCatch body-value (blocked)
- L7466: tryCatch inner
- L7574: while_ CCState threading (blocked)

### TASK 1: L4197 — FuncsSupported preservation (CONCRETE APPROACH)

```lean
have hfuncs_supp' : ∀ (i : Nat) (fd : Core.FuncClosure), sc'.funcs[i]? = some fd → fd.body.supported = true :=
    sorry
```

**The proof**: Core.step? either (a) preserves `sc.funcs` (most cases) or (b) pushes a new FuncClosure (functionDef case).

1. First, `lean_goal` at L4197 to see what's in scope. You have `hcstep` (the Core step) and `hfuncs_supp` (old invariant).

2. Try this EXACT tactic sequence:
```lean
fun i fd hfd => by
  -- hcstep : Core.Steps sc [ev] sc'
  -- Get the single step
  obtain ⟨hstep_eq⟩ := hcstep
  -- Case split on what the step was
  cases hsc : sc.expr <;> simp [hsc, Core.step?] at hstep_eq
  all_goals sorry
```

3. For each case, most will show `sc'.funcs = sc.funcs` so `hfuncs_supp i fd (hfd ▸ rfl)` or `exact hfuncs_supp i fd hfd` closes it.

4. For `functionDef`: `sc'.funcs = sc.funcs.push ⟨params, body, ...⟩`. Use:
```lean
simp [Array.getElem?_push] at hfd
cases Nat.lt_or_eq_of_le (Array.getElem?_push_le hfd) with
| inl h => exact hfuncs_supp i fd (by rwa [Array.getElem?_push_lt (by exact h)] at hfd)
| inr h => -- i = sc.funcs.size, fd = new closure, body from source → supported from hsupp
  sorry
```

5. USE `lean_multi_attempt` BEFORE editing. Try 3-5 different tactics and see which one makes progress.

### IF L4197 IS TRULY BLOCKED: explain WHY in your log and move to L7236 (functionDef)

L7236 should be simpler — both sides push a new closure. The convertExpr of the function body gives the converted body.

## PRIORITY: L4197 ONLY until it's closed. Nothing else matters.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
