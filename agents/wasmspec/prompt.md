# wasmspec — Close non-hnoerr CC sorries + begin Core Fix D

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## HNOERR SORRIES: BLOCKED — DO NOT ATTEMPT
jsspec discovered the root cause: Flat has Fix D error propagation but Core does NOT.
When a sub-step produces `.error msg`, Flat collapses to `.lit .undefined` but Core
keeps the wrapper (`.assign name sr.expr`). CC_SimRel breaks.

**Fix**: Add Fix D to Core.step? (mirror Flat's error propagation). This is a multi-run
effort. For now, focus on non-hnoerr sorries.

## STATUS (18:05 Mar 30)
- CC: 44 sorries. 22 are hnoerr (BLOCKED). 2 forIn/forOf (unprovable). **20 closable.**

## YOUR TASK: Close non-hnoerr CC sorries

### TARGET 1: Captured variable case (L3092)

This is the `| some idx =>` branch of the `.var name` case where `lookupEnv envMap name = some idx`.
The converted expression is `.getEnv (.var envVar) idx` — a closure environment access.

Use `lean_goal` at L3092 to see the full context. The proof needs:
1. Show Flat.step? on `.getEnv (.var envVar) idx` corresponds to Core.step? on `.var name`
2. Use `EnvCorrInj` to relate the env lookup results
3. HeapInj to relate heap accesses (closure env is stored on heap)

This might need a helper theorem about `getEnv` stepping. Check with `lean_local_search "getEnv"`.

### TARGET 2: Value sub-cases (L3953, L4699, L5024, L5123)

L3953: `.call callee args` where callee is a value — arg stepping or call execution.
L4699: `.setProp obj prop value` where obj is a value — value sub-case.
L5024: `.objectLit props` where all props are values — heap allocation.
L5123: `.arrayLit elems` where all elems are values — heap allocation.

For L5024 and L5123 (all values): these produce a heap allocation. The Core side does
`.objectLit props` → evaluates all props → allocates. The Flat side should do the same.
Use `lean_goal` to see what's needed, then construct the Core step.

### TARGET 3: Begin Core Fix D implementation

Create `.lake/_tmp_fix/Core_semantics_fix_d.lean` as a staging file with:

For EACH of the 28 `match step? { s with expr := sub }` positions in Core/Semantics.lean,
add an error propagation arm:
```lean
-- BEFORE (current):
match step? { s with expr := sub } with
| some (t, sa) =>
    some (t, pushTrace { sa with expr := wrapper sa.expr, trace := s.trace } t)
| none => none

-- AFTER (with Fix D):
match step? { s with expr := sub } with
| some (.error msg, sa) =>
    some (.error msg, pushTrace { s with expr := .lit .undefined, env := sa.env, heap := sa.heap } (.error msg))
| some (t, sa) =>
    some (t, pushTrace { sa with expr := wrapper sa.expr, trace := s.trace } t)
| none => none
```

Write this as a DIFF file showing each change. Include line numbers from Core/Semantics.lean.
Also list the Core_step?_*_error theorems that will be needed in CC (analogous to the
Flat_step?_*_error theorems you already wrote).

**IMPORTANT**: Do NOT edit Core/Semantics.lean directly yet. Just stage the changes.
Editing would break the build until CC is also updated.

## DO NOT TOUCH:
- ANFConvertCorrect.lean (proof agent owns this)
- hnoerr/hev_noerr sorries (BLOCKED until Core Fix D)
- forIn/forOf stubs (unprovable)

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean`
3. Log to agents/wasmspec/log.md

## TARGET: Close at least 2 non-hnoerr sorries → CC from 44 to ≤42
