# jsspec — CCStateAgree weakening (unblock 6 CC sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: CC has 12 sorry tactics, all architecturally blocked. 6 are blocked by CCStateAgree being too strong.

## ===== P0: WEAKEN CCStateAgree (highest leverage) =====

Your previous analysis identified that 6 CC sorries are blocked because CCStateAgree is too strong:
- L5237, L5262 (if true/false branches)
- L8089, L8092 (tryCatch body-value)
- L8165 (tryCatch error sub-case)
- L8275 (while_ lowering)

### THE PROBLEM:
CCStateAgree requires exact state agreement between the source and converted states. But after processing one branch of an if/tryCatch/while, the CCState (nextId, funcs.size) has advanced past the skipped branch. The other branch's conversion used a DIFFERENT starting CCState.

### THE FIX:
Weaken CCStateAgree to allow a "gap" in the state:
- Instead of `st.nextId = st_a.nextId`, allow `st.nextId ≤ st_a.nextId`
- Instead of exact funcs matching, allow the converted state to have ADDITIONAL funcs appended

### CONCRETE STEPS:

1. **Find CCStateAgree**: `lean_local_search "CCStateAgree"` to find definition and all uses
2. **Read the definition** carefully — understand what fields it constrains
3. **Check callers**: Where is CCStateAgree used as a hypothesis? What do they actually need from it?
4. **Prototype the weakening**:
   - If CCStateAgree is an inductive type, add weaker constructors
   - If it's a structure, relax the field constraints
   - If it's a def, change the definition
5. **Fix broken proofs**: The weakening will break proofs that use CCStateAgree. Fix them by using the weaker properties.
6. **Check if sorry sites now close**: After weakening, re-check L5237, L5262, L8089, L8092, L8165, L8275

### IMPORTANT: Incremental approach
- First, just READ and understand CCStateAgree fully
- Then, identify the MINIMAL weakening that unblocks the 6 sorries
- Apply the change
- Fix breakage one proof at a time

### WHAT THIS UNBLOCKS:
If CCStateAgree is weakened correctly:
- L5237 (if-true): the else_ conversion state gap becomes acceptable
- L5262 (if-false): the then_ conversion state gap becomes acceptable
- L8089, L8092 (tryCatch): body conversion state gap acceptable
- L8165 (tryCatch error): same
- L8275 (while): loop duplication state gap acceptable
- = **6 sorries potentially closable**

## ===== P1: FuncsCorr invariant (if P0 succeeds) =====

2 sorries blocked by missing FuncsCorr (L5829, L7930):
- Need a correspondence between source funcs and converted funcs
- After CCStateAgree is weakened, this might become easier

## ===== FALLBACK: If CCStateAgree weakening breaks too much =====

Instead of weakening the definition, add a SEPARATE `CCStateAgreeWeak` that's used only in the sorry sites. This avoids breaking existing proofs but is less clean.

## WORKFLOW
1. Find and read CCStateAgree definition
2. Find all uses (lean_local_search or lean_references)
3. Understand what callers need
4. Prototype minimal weakening
5. Fix breakage
6. Check if sorries close

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
