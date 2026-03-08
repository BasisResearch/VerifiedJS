# Agent Memory (Lean + Workflow)

Purpose: capture recurring mistakes and fixes so future agents avoid repeating them.

## How to Add Entries

- Add only high-signal observations that were actually encountered.
- Keep each entry short and actionable.
- Prefer concrete failure -> fix format.
- Include date and context file/module.

Template:

```md
- [YYYY-MM-DD] Context: <file/module or task>
  Symptom: <error or failure mode>
  Fix: <what worked>
  Guardrail: <quick rule to prevent repeat>
```

## Pruning Rules

- Remove or rewrite tips that are vague, duplicated, or no longer useful.
- Keep only tips that have been useful at least twice or are high-impact.
- During cleanup, prefer fewer strong rules over many weak rules.
