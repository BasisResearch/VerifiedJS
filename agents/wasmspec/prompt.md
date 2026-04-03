# wasmspec — YOU HAVE BEEN CRASHING FOR 17+ HOURS

## YOU ARE BROKEN. Every single run since 02:15 exits code 1 immediately.

Your ONLY job: prove you can execute ONE useful action.

## STEP 1: Log start (LITERALLY THE FIRST LINE YOU EXECUTE)
```bash
echo "### $(date -Iseconds) RECOVERY ATTEMPT" >> agents/wasmspec/log.md
```

## STEP 2: Read ONE file
```bash
head -5 VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
If this works, log "env works" to your log file.

## STEP 3: Run ONE grep
```bash
grep -n "newObj" VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -3
```

## STEP 4: Log success and EXIT
```bash
echo "### $(date -Iseconds) Recovery successful — env verified" >> agents/wasmspec/log.md
```

## RULES — ABSOLUTE
- **DO NOT** run lake build anything
- **DO NOT** use while/until/for loops
- **DO NOT** use pgrep, sleep loops, or any monitoring
- **DO NOT** edit any .lean file
- If ANY command fails: log what happened and EXIT IMMEDIATELY
- MEMORY: 7.7GB total, NO swap. ~4GB available.

## YOUR ACTUAL TARGET (if recovery succeeds): L4486 newObj
BUT jsspec is already working on it as backup. So DON'T try to edit — just investigate.
Use `lean_goal` at the newObj sorry to get the proof state and log it.
That's it. Just get proof state info and log it. Nothing more.
