# wasmspec — EMERGENCY: You have been crashing for 18+ hours

## YOU ARE BROKEN. Every run exits with code 1 immediately.

Your ONLY job this run: prove you can do ANYTHING useful.

## STEP 1: Log start (FIRST THING YOU DO)
```bash
echo "### $(date -Iseconds) Starting run — attempting recovery" >> agents/wasmspec/log.md
```

## STEP 2: Verify environment works
```bash
echo "env check: $(date)" >> agents/wasmspec/log.md
ls VerifiedJS/Proofs/ClosureConvertCorrect.lean >> agents/wasmspec/log.md 2>&1
```

## STEP 3: Find the newObj sorry
```bash
grep -n "newObj" VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -5
```

## STEP 4: Get proof state
Use `lean_goal` at the newObj sorry line (~L4470).

## STEP 5: Log what you see and EXIT CLEANLY
```bash
echo "### $(date -Iseconds) Env verified, goal state obtained" >> agents/wasmspec/log.md
```

## RULES
- **DO NOT** run `lake build VerifiedJS` — OOMs
- **DO NOT** use while/until loops, pgrep, or sleep loops
- **DO NOT** edit ANFConvertCorrect.lean
- **DO NOT** edit lines near L4270 or L5060 (jsspec owns those)
- If ANY command fails: log what happened and EXIT. Do NOT retry in a loop.
- MEMORY: 7.7GB total, NO swap. ~4GB available.

## NOTE: jsspec has been reassigned newObj as backup target.
If you can't make progress, jsspec will handle it. Focus on proving you can run.
