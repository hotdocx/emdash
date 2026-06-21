#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

# Positions are zero-based after the rule head. They cover the generic
# categories, families, and endpoints that Lambdapi normally infers.
INFERRED_SLOTS = {
    "comp_fapp0": (0, 1, 2, 3),
    "comp_cat_fapp0": (0, 1, 2),
    "comp_catd_fapp0": (0, 1, 2, 3),
    "fapp0": (0, 1),
    "fapp1_func": (0, 1, 3, 4),
    "fapp1_fapp0": (0, 1, 3, 4),
    "tapp0_fapp0": (0, 1, 2, 3),
    "tapp1_func": (0, 1, 2, 3, 4, 5),
    "tapp1_fapp0": (0, 1, 2, 3, 4, 5),
    "tdapp0_fapp0": (0, 1, 2, 3, 4),
    "fdapp0_fapp0": (0, 1, 2, 3, 4),
}


@dataclass(frozen=True)
class Candidate:
    line: int
    head: str
    slot: int
    argument: str


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        if block_depth:
            if text.startswith("/*", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("*/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        if not in_string and text.startswith("//", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if not in_string and text.startswith("/*", i):
            block_depth = 1
            out.extend("  ")
            i += 2
            continue

        char = text[i]
        if char == '"' and (i == 0 or text[i - 1] != "\\"):
            in_string = not in_string
        out.append(char)
        i += 1
    return "".join(out)


def split_top_level(term: str) -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    round_depth = 0
    square_depth = 0
    brace_depth = 0
    in_string = False

    for i, char in enumerate(term):
        if char == '"' and (i == 0 or term[i - 1] != "\\"):
            in_string = not in_string
        if not in_string:
            if char == "(":
                round_depth += 1
            elif char == ")":
                round_depth -= 1
            elif char == "[":
                square_depth += 1
            elif char == "]":
                square_depth -= 1
            elif char == "{":
                brace_depth += 1
            elif char == "}":
                brace_depth -= 1

        if (
            not in_string
            and char.isspace()
            and round_depth == 0
            and square_depth == 0
            and brace_depth == 0
        ):
            if current:
                parts.append("".join(current))
                current = []
        else:
            current.append(char)

    if current:
        parts.append("".join(current))
    return parts


def rule_commands(text: str) -> list[tuple[int, str]]:
    lines = text.splitlines()
    commands: list[tuple[int, str]] = []
    i = 0
    while i < len(lines):
        if not re.match(r"^rule\b", lines[i]):
            i += 1
            continue
        start = i + 1
        command = [lines[i]]
        while not re.search(r";\s*$", lines[i]):
            i += 1
            if i >= len(lines):
                break
            command.append(lines[i])
        commands.append((start, "\n".join(command)))
        i += 1
    return commands


def candidates(path: Path) -> list[Candidate]:
    text = strip_comments(path.read_text(encoding="utf-8"))
    found: list[Candidate] = []
    for command_line, command in rule_commands(text):
        clauses = re.split(r"\nwith\s+", command)
        clause_offset = 0
        for clause_text in clauses:
            clause_line = command_line + clause_offset
            clause = re.sub(r"^rule\s+", "", clause_text)
            lhs = clause.split("↪", 1)[0].strip()
            parts = split_top_level(lhs)
            clause_offset += clause_text.count("\n")
            if not parts or not parts[0].startswith("@"):
                continue

            head = parts[0][1:]
            slots = INFERRED_SLOTS.get(head)
            if slots is None:
                continue
            arguments = parts[1:]

            for slot in slots:
                if slot >= len(arguments):
                    continue
                argument = arguments[slot]
                if not argument.startswith("("):
                    continue

                variables = set(re.findall(r"\$[A-Za-z0-9_']+", argument))
                if not variables:
                    continue
                other_arguments = " ".join(
                    value for index, value in enumerate(arguments) if index != slot
                )
                if all(variable in other_arguments for variable in variables):
                    found.append(
                        Candidate(
                            line=clause_line,
                            head=head,
                            slot=slot + 1,
                            argument=argument,
                        )
                    )
    return found


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Advisory scan for reconstructible compound terms in inferred "
            "rewrite-rule LHS slots."
        )
    )
    parser.add_argument(
        "file",
        nargs="?",
        type=Path,
        default=Path("emdash3_2.lp"),
        help="Lambdapi source to scan (default: emdash3_2.lp).",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON.")
    args = parser.parse_args()

    path = args.file if args.file.is_absolute() else ROOT / args.file
    found = candidates(path)
    clauses = {(item.line, item.head) for item in found}

    if args.json:
        print(
            json.dumps(
                {
                    "file": str(path),
                    "candidate_clauses": len(clauses),
                    "candidate_slots": len(found),
                    "candidates": [asdict(item) for item in found],
                },
                indent=2,
            )
        )
        return 0

    print(
        f"{path}: {len(found)} reconstructible compound slot(s) "
        f"across {len(clauses)} rule clause(s)"
    )
    for item in found:
        print(f"{item.line}: @{item.head} slot {item.slot}: {item.argument}")
    print()
    print(
        "Advisory only: constructor and pair patterns may be intentional "
        "discriminators. Probe each proposed replacement with `_`."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
