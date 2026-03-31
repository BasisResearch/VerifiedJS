# wasmspec — Close CC value sub-cases + functionDef + tryCatch + callee/newObj

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! CRITICAL BUG FROM LAST RUN !!
Your previous session got PERMANENTLY STUCK in `while pgrep -f "lake build"` because
the while loop's own shell command string contains "lake build", so pgrep matches ITSELF.
**THIS KILLED YOUR ENTIRE SESSION — 10+ HOURS WASTED.**

### ABSOLUTE RULES FOR PROCESS WAITING:
1. **NEVER use `while` loops** — not for pgrep, not for anything, not ever
2. **NEVER use `until` loops** — same problem
3. **NEVER use `sleep` in a loop** — you will get stuck
4. `lake serve` processes are PERMANENT. `pgrep -x lake` will ALWAYS return 0.
5. To check if a BUILD is running: `pgrep -f "lake build"` (but NEVER in a loop)
6. If a build IS running: just SKIP and do something else. Do NOT wait.
7. If you need to build: just run the build command directly. If it fails, try later.

## MEMORY: 7.7GB total, NO swap.

## STATE (01:05): CC has 19 grep-sorry, ~16 real sorries

### Remaining sorry breakdown:
- **2 unprovable stubs** (L1502-1503 forIn/forOf): DO NOT TOUCH
- **2 convertExpr_not_lit** (L2663, L2773): jsspec owns
- **1 captured variable** (L2857): jsspec owns
- **2 CCState if-true** (L3176): jsspec owns
- **2 CCState if-false** (L3198): jsspec owns
- **1 CCState while_** (L5237): jsspec owns
- **2 callee/newObj** (L3692, L3693): YOUR TARGET
- **1 getIndex mismatch** (L4261): possibly unprovable
- **1 setIndex value sub-case** (L4433): YOUR TARGET
- **1 objectLit all-values** (L4755): YOUR TARGET
- **1 arrayLit all-values** (L4938): YOUR TARGET
- **1 functionDef** (L5116): YOUR TARGET
- **1 tryCatch** (L5206): YOUR TARGET

## YOUR TARGETS (7 sorries):

### TARGET 1: Value sub-cases — HIGHEST PRIORITY

These are ALL the same pattern: all sub-expressions are values, so both Core and Flat
take one matching step (allocation, property access, etc.).

**L3692**: `| some cv => sorry -- callee is value: arg stepping or call execution`
**L3693**: `| newObj f args => sorry`
**L4433**: `| some cv => sorry -- value sub-case (heap reasoning needed)`
**L4755**: `sorry -- all props are values: heap allocation`
**L4938**: `sorry -- all elements are values: heap allocation`

APPROACH for each:
1. `lean_goal` at the sorry line → read FULL goal
2. `lean_local_search "allValues"` and `lean_local_search "value_step"` for helpers
3. When all sub-exprs are values, Core.step? and Flat.step? should BOTH take exactly
   one step. The proof is: construct the matching steps, show results correspond.
4. `lean_multi_attempt` with:
   ```
   ["simp_all", "exact ⟨_, _, rfl, rfl⟩", "constructor <;> simp_all",
    "refine ⟨_, _, ?_, ?_⟩ <;> simp_all", "aesop"]
   ```
5. If the goal has `∃ sf' evs, Flat.Steps ...`, build the witness explicitly:
   `exact ⟨{sf with expr := ..., heap := ...}, [ev], .tail ⟨by unfold Flat.step?; simp⟩ (.refl _), ...⟩`

### TARGET 2: functionDef (L5116)
`| functionDef fname params body isAsync isGen => sorry`

functionDef creates a closure and binds fname in env. Both Core and Flat should
produce equivalent bindings. `lean_goal` → look for closure value correspondence.

### TARGET 3: tryCatch (L5206)
`| tryCatch body catchParam catchBody finally_ => sorry`

Sets up exception handler context. Core enters try body; Flat enters converted body
with catch frame pushed.

## TACTIC FOR Flat_step? PROOFS (proven pattern):
The supervisor proved 22 Flat stepping theorems with this approach:
- Simple cases: `simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]`
- Complex (getIndex, setProp, setIndex, call, binary):
  `cases fe with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]`

Use this pattern when you need to prove Flat stepping lemmas.

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf stubs (L1502-1503) — unprovable
- CCState threading sorries (L2857, L3176, L3198, L5237) — jsspec owns these
- convertExpr_not_lit (L2663, L2773) — jsspec owns these
- getIndex string mismatch (L4261) — possibly unprovable

## WORKFLOW:
1. `lean_goal` at the sorry line — read the FULL goal
2. `lean_multi_attempt` with 6-8 tactics
3. If nothing closes it in 10 minutes, MOVE TO THE NEXT ONE
4. Log what you tried and why it failed

## TARGET: Close at least 3 of your 7 assigned sorries → CC from 19 to ~16
