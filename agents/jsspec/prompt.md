# jsspec — Close remaining CC sorries: FuncsSupported + CCStateAgree + functionDef

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: AMAZING WORK! You closed ALL 8 Core_step_preserves_supported cases! CC down from 30→13 real sorries.

Remaining 13 sorries in ClosureConvertCorrect.lean:

| Line | Category | Description |
|------|----------|-------------|
| L3930 | FuncsSupported | closure.body.supported needs FuncsSupported invariant |
| L4146 | HeapInj staging | proof temporarily sorry'd during HeapInj refactor |
| L4475 | CCStateAgree | if-true: st' vs then_-only state |
| L4498 | CCStateAgree | if-false: CCStateAgree |
| L5062 | funcs correspondence | non-consoleLog function call: sf.funcs[idx] ↔ sc.funcs[idx] |
| L5270 | semantic mismatch | f not a value: Core allocates vs Flat steps |
| L5278 | semantic mismatch | non-value arg: Core allocates vs Flat steps |
| L5916 | UNPROVABLE | getIndex string both-values |
| L7158 | functionDef | entire functionDef case sorry'd |
| L7315 | tryCatch | body-value: CCStateAgree |
| L7316 | tryCatch | with finally: CCStateAgree blocked |
| L7388 | tryCatch | (check context) |
| L7496 | while_ | CCState threading: duplicated sub-expressions |

## TASK 1: Close L3930 (FuncsSupported invariant) — HIGHEST PRIORITY

This is in the call case of Core_step_preserves_supported. When `callee = .lit (.function idx)` and `s.funcs[idx] = some closure`, the result is `tryCatch closure.body ...`. You need `closure.body.supported`.

**Approach**: Add a `FuncsSupported` hypothesis to Core_step_preserves_supported:
```lean
(hfuncs : ∀ (i : Nat) (c : Core.Closure), s.funcs[i]? = some c → c.body.supported = true)
```

Then at L3930:
```lean
have hcl := hfuncs idx closure ‹_›
simp [Core.Expr.supported, Bool.and_eq_true]; exact hcl
```

You'll also need to update the call site at L4119 to provide this hypothesis. Check what the caller has available — it likely needs to thread a funcs invariant from the simulation relation.

## TASK 2: Close L7158 (functionDef case) — HIGH PRIORITY

This is the entire `functionDef` constructor in the main CC simulation theorem. Use `lean_goal` at L7158 to see what's needed. Pattern:
- Source: `functionDef fname params body isAsync isGen` steps to allocate a closure
- CC: convertExpr produces the closure conversion, Flat should step similarly
- Key: show the converted expression steps to the right state

## TASK 3: Address CCStateAgree sorries (L4475, L4498, L7315, L7316, L7496)

These are all the same root cause: CCStateAgree fails when a resolution step discards a branch whose conversion advanced nextId/funcs.size.

**For L4475/L4498 (if-true/false):** The witness state `st_a` needs to account for both branches' conversion. Try:
- Use `lean_goal` to see the exact obligation
- Check if `convertExpr_state_determined` can help select the right witness
- If the obligation is `st_a.nextId = st'.nextId` where st' went through both branches but we only took one: you may need to show the other branch's conversion has zero effect (no functionDef nodes)

**For L7315/L7316 (tryCatch):** Similar CCStateAgree issue with catch/finally branches.

**For L7496 (while_):** While_ lowering duplicates sub-expressions → CCState diverges.

If these are architecturally blocked (as jsspec log from 2026-03-31 analyzed), consider:
1. Adding a `NoFunctionDef` predicate and proving it for the discarded branch
2. Or relaxing the sim relation to not require CCStateAgree on output

## TASK 4: L5916 (UNPROVABLE) — Consider removing or axiomatizing

If this is truly unprovable (getIndex string mismatch), add a `sorry` comment explaining why and move on. Don't waste time here.

## PRIORITY ORDER
1. L3930 — FuncsSupported (quick, finishes Core_step_preserves_supported)
2. L7158 — functionDef (large but tractable)
3. L4475/L4498 — if CCStateAgree (may need architectural change)
4. L7315/L7316/L7496 — tryCatch/while CCStateAgree
5. L4146 — HeapInj staging (deferred)
6. Skip L5916 (unprovable)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
