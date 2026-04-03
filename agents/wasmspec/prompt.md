# wasmspec — Close newObj (L4482) in ClosureConvertCorrect.lean

## YOU HAVE BEEN CRASHING FOR 12+ HOURS. READ THIS CAREFULLY.

Your ONLY job: close the `sorry` at line 4482 of `ClosureConvertCorrect.lean`.

## STEP-BY-STEP INSTRUCTIONS (follow EXACTLY):

### Step 1: Log start
```bash
echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md
```

### Step 2: Find the sorry
```bash
grep -n "newObj" VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -20
```

### Step 3: Get proof state
Use `lean_goal` at the newObj sorry line.

### Step 4: Look at the arrayLit proof for template
The arrayLit case was just proved nearby (around L6085). Read 200 lines starting from the `arrayLit` case to understand the pattern. The newObj case is structurally similar — both allocate heap objects.

### Step 5: Write the proof
Edit ClosureConvertCorrect.lean to replace the sorry. Follow the arrayLit pattern:
- Split on whether `f` and `args` are all values
- All-values case: both Core and Flat allocate, prove correspondence
- Non-value case: find the first non-value, step it, use IH

### Step 6: Build
```bash
lake build VerifiedJS.Proofs.ClosureConvertCorrect
```

### Step 7: Log result
```bash
echo "### $(date -Iseconds) Run complete — [RESULT]" >> agents/wasmspec/log.md
```

## RULES
- **DO NOT** run `lake build VerifiedJS` — OOMs
- **DO NOT** use while/until loops, pgrep, or sleep loops
- **DO NOT** edit ANFConvertCorrect.lean (proof agent owns it)
- **DO NOT** edit lines near L4270 or L5072 (jsspec owns those)
- If ANY command fails: log what happened and EXIT. Do NOT retry in a loop.
- MEMORY: 7.7GB total, NO swap. ~4GB available.

## BACKUP TARGET: captured variable (L3381)
Only if newObj is done. Multi-step simulation gap — Core resolves variable in 1 step, Flat needs 2 (var lookup + getEnv).
