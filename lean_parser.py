"""Lightweight Lean 4 parser using Lark for extracting declarations and match cases."""
from lark import Lark, Transformer, v_args, Token
from dataclasses import dataclass, field
from typing import Optional

# Grammar: enough to parse top-level declarations and match case structure.
# NOT a full Lean parser — just enough for code archaeology.
LEAN_GRAMMAR = r"""
start: item*

?item: decl | namespace_block | section_block | open_cmd | set_option | import_cmd | OTHER_LINE

decl: modifiers decl_kind NAME sig decl_body
modifiers: (MODIFIER)*
decl_kind: "theorem" | "lemma" | "def" | "inductive" | "structure" | "instance" | "class" | "axiom" | "abbrev"
sig: sig_token*
decl_body: ":=" body_content
         | "where" body_content
         | /* empty */

body_content: (match_expr | other_body_token)*
match_expr: "match" match_tokens "with" match_cases
match_cases: match_case+
match_case: "|" case_pattern "=>" case_body
case_pattern: pattern_token+
case_body: (nested_match | case_token)*
nested_match: "match" match_tokens "with" match_cases

namespace_block: "namespace" NAME NEWLINE item* "end" NAME
section_block: "section" NAME? NEWLINE item*
open_cmd: "open" /[^\n]*/
set_option: "set_option" /[^\n]*/
import_cmd: "import" /[^\n]*/

// Tokens — permissive, we don't need to type-check
sig_token: /(?!:=|where)[^\n]/ | NEWLINE /\s+(?!theorem|lemma|def|inductive|structure|instance|class|end\s|namespace\s)/
match_tokens: /(?!with\b)[^\n]/ | NEWLINE /\s+(?!with\b)/
pattern_token: /(?!=>)[^\n|]/
case_token: /(?!\|(?:\s*[.«]|\s+_\s*=>))[^\n]/ | NEWLINE /\s+(?!\|)/
other_body_token: /(?!match\b|\|(?:\s*[.«]))[^\n]/ | NEWLINE /\s+(?!theorem|lemma|def|inductive|structure|instance|class|end\s|namespace\s)/

MODIFIER: "private" | "protected" | "noncomputable" | "partial" | "mutual" | "unsafe"
NAME: /[a-zA-Z_«][a-zA-Z0-9_.'»?]*/
OTHER_LINE: /[^\n]*/ NEWLINE
NEWLINE: /\n/

%ignore /[ \t]+/
%ignore /--[^\n]*/
"""

# The full lark grammar above is too ambitious for Lean's syntax.
# Instead, use a simpler two-pass approach:
# Pass 1: Split file into top-level declarations (by indentation)
# Pass 2: For each `def`, split match body into cases

def parse_lean_file(content: str) -> dict:
    """Parse a Lean file into declarations and their match cases.
    Returns: {
        'declarations': [{'kind', 'name', 'line', 'end_line', 'body', 'sorry', 'cases': {...}}],
    }
    """
    lines = content.splitlines()
    decls = []

    # Pass 1: Find declarations by matching unindented lines
    i = 0
    while i < len(lines):
        line = lines[i]
        # Match declaration keywords at start of line (possibly with modifiers)
        stripped = line.lstrip()
        indent = len(line) - len(stripped)

        kind = None
        name = None
        for kw in ('theorem', 'lemma', 'def', 'inductive', 'structure', 'instance', 'class', 'axiom', 'abbrev'):
            # Check with optional modifiers
            for prefix in ('', 'private ', 'protected ', 'noncomputable ', 'partial ', 'private partial ', 'noncomputable partial '):
                if stripped.startswith(prefix + kw + ' '):
                    kind = kw
                    rest = stripped[len(prefix + kw):].strip()
                    # Extract name (handle names with ? and «»)
                    name_chars = []
                    for ch in rest:
                        if ch in ' (:{\n':
                            break
                        name_chars.append(ch)
                    name = ''.join(name_chars)
                    break
            if kind:
                break

        if not kind:
            i += 1
            continue

        # Find end of declaration: next unindented declaration or end/namespace
        start_line = i
        i += 1
        while i < len(lines):
            if not lines[i].strip():
                i += 1
                continue
            next_indent = len(lines[i]) - len(lines[i].lstrip())
            if next_indent <= indent:
                next_stripped = lines[i].lstrip()
                is_decl = any(next_stripped.startswith(p + k + ' ')
                    for k in ('theorem', 'lemma', 'def', 'inductive', 'structure', 'instance', 'class', 'axiom', 'abbrev', 'end ', 'namespace ', 'section ')
                    for p in ('', 'private ', 'protected ', 'noncomputable ', 'partial ', 'private partial '))
                if is_decl or next_stripped.startswith('#') or next_stripped.startswith('set_option'):
                    break
            i += 1

        body = '\n'.join(lines[start_line:i])
        has_sorry = 'sorry' in body and kind in ('theorem', 'lemma', 'def')

        # Pass 2: Extract match cases for defs
        cases = _extract_cases(lines[start_line:i])

        decls.append({
            'kind': kind,
            'name': name,
            'line': start_line + 1,
            'end_line': i,
            'body': body,
            'sorry': has_sorry,
            'cases': cases,
            'num_lines': i - start_line,
        })

    return {'declarations': decls}


def _extract_cases(lines: list[str]) -> dict[str, str]:
    """Extract match cases from a list of lines belonging to a declaration.
    Returns dict mapping case label to case body."""
    cases = {}
    current_label = None
    current_lines = []

    for line in lines:
        stripped = line.lstrip()
        # Detect case pattern: starts with `| .name` or `| «name»`
        if stripped.startswith('| .') or stripped.startswith('| \u00ab'):
            # Save previous case
            if current_label is not None and current_lines:
                cases[current_label] = '\n'.join(current_lines)

            # Parse case name
            after_pipe = stripped[2:].lstrip()
            if after_pipe.startswith('.'):
                # .name or .name(args) or .«name»
                rest = after_pipe[1:]
                name_chars = []
                for ch in rest:
                    if ch in ' (\n,|':
                        break
                    name_chars.append(ch)
                current_label = ''.join(name_chars)
            elif after_pipe.startswith('\u00ab'):
                # «name»
                current_label = after_pipe[1:].split('\u00bb')[0]
            else:
                current_label = after_pipe.split()[0] if after_pipe.split() else '?'

            current_lines = [line]
        elif current_label is not None:
            current_lines.append(line)

    # Save last case
    if current_label is not None and current_lines:
        cases[current_label] = '\n'.join(current_lines)

    return cases


def parse_step_function(content: str, func_name: str = 'step?') -> tuple[dict[str, str], str]:
    """Extract cases from a specific step function.
    Returns (cases_dict, full_body_string)."""
    result = parse_lean_file(content)
    for decl in result['declarations']:
        if decl['name'] == func_name:
            return decl['cases'], decl['body']
    return {}, ''


def diff_cases(old: dict[str, str], new: dict[str, str]) -> tuple[dict, dict, dict]:
    """Diff two case dicts. Returns (added, removed, changed)."""
    added = {k: v for k, v in new.items() if k not in old}
    removed = {k: v for k, v in old.items() if k not in new}
    changed = {k: (old[k], new[k]) for k in old if k in new and old[k] != new[k]}
    return added, removed, changed


# ── Self-test ──
if __name__ == '__main__':
    import sys
    path = sys.argv[1] if len(sys.argv) > 1 else 'VerifiedJS/Core/Semantics.lean'
    content = open(path).read()

    result = parse_lean_file(content)
    decls = result['declarations']
    print(f'{len(decls)} declarations in {path}')

    theorems = [d for d in decls if d['kind'] in ('theorem', 'lemma')]
    defs = [d for d in decls if d['kind'] == 'def']
    print(f'  {len(theorems)} theorems/lemmas, {len(defs)} defs')
    sorry_count = sum(1 for d in decls if d['sorry'])
    print(f'  {sorry_count} with sorry')

    # Show step? cases
    cases, body = parse_step_function(content, 'step?')
    print(f'\nstep?: {len(cases)} cases, {len(body.splitlines())} lines')
    for k in sorted(cases)[:8]:
        print(f'  | .{k}: {cases[k].count(chr(10))+1}L')
    if len(cases) > 8:
        print(f'  ... and {len(cases)-8} more')
