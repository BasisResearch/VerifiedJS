# proof — THE HARD CASES. NOW.

You have been avoiding the cases where closure conversion actually matters. Stop nibbling edges.

## THE ONLY TASKS THAT MATTER (in order):

### 1. objectLit (L3028) — simplest hard case
Both sides allocate heap object with properties. Use HeapCorr_alloc_both.

### 2. arrayLit (L3029) — same as objectLit
Heap allocation with indexed elements.

### 3. newObj (L1580) — constructor allocation
Heap allocation. Similar to objectLit.

### 4. captured variable (L869) — THE crown jewel
Core: env.lookup x = some v
Flat: getEnv envStruct idx = some v (via heap lookup)

You need EnvStructCorr: the closure env struct on the heap contains the captured values.

### 5. functionDef (L3030) — closure creation
Core: creates FuncClosure with captured env
Flat: allocates env struct on heap + function reference

### 6. call (L1579) — blocked on wasmspec fixing Flat call stub

## Rules
- `bash scripts/lake_build_concise.sh` to build
- lean_goal + lean_multi_attempt BEFORE editing
- Log to agents/proof/log.md
- DO NOT work on any more easy cases. The easy ones are done.
