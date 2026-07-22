#!/usr/bin/env python3
from __future__ import annotations

import argparse
import collections
import re
import sys
from dataclasses import dataclass
from pathlib import Path


LOCATION_RE = re.compile(r"\[([^:\]]+\.lp):([0-9]+)(?::[0-9]+)?")
LOCATION_LINE_RE = re.compile(r"^\[[^:\]]+\.lp:[0-9]+")
HEAD_RE = re.compile(r"^t ≔ @?([^\s(]+)")
PARTICIPANT_RE = re.compile(r"^\s+with @?([^\s(]+)")


@dataclass
class WarningInventory:
    categories: collections.Counter[str]
    locations: collections.Counter[str]
    term_heads: collections.Counter[str]
    rule_families: collections.Counter[tuple[str, str]]
    parser_issues: collections.Counter[str]


def read_lines(path: str | None) -> list[str]:
    if path is None or path == "-":
        return sys.stdin.read().splitlines()
    return Path(path).read_text(encoding="utf-8", errors="replace").splitlines()


def location_before(lines: list[str], index: int) -> str | None:
    for line in reversed(lines[max(0, index - 3) : index + 1]):
        match = LOCATION_RE.search(line)
        if match:
            return f"{match.group(1)}:{match.group(2)}"
    return None


def print_counts(title: str, counts: collections.Counter[str], limit: int) -> None:
    if not counts:
        return
    print()
    print(title)
    for name, count in counts.most_common(limit):
        print(f"{count:6d}  {name}")


def critical_pair_shape(
    lines: list[str], index: int
) -> tuple[str | None, list[str]]:
    """Return the overlap head and the two rules printed by Lambdapi."""
    head: str | None = None
    participants: list[str] = []
    for line in lines[index + 1 :]:
        if LOCATION_LINE_RE.match(line):
            break
        if head is None:
            match = HEAD_RE.match(line)
            if match:
                head = match.group(1)
        match = PARTICIPANT_RE.match(line)
        if match:
            participants.append(match.group(1))
    return head, participants


def warning_inventory(lines: list[str]) -> WarningInventory:
    categories: collections.Counter[str] = collections.Counter()
    locations: collections.Counter[str] = collections.Counter()
    term_heads: collections.Counter[str] = collections.Counter()
    rule_families: collections.Counter[tuple[str, str]] = collections.Counter()
    parser_issues: collections.Counter[str] = collections.Counter()

    for index, line in enumerate(lines):
        category: str | None = None
        if line == "Unjoinable critical pair:":
            category = "unjoinable critical pair"
            head, participants = critical_pair_shape(lines, index)
            if head is None:
                parser_issues["critical pair without a term head"] += 1
            else:
                term_heads[head] += 1
            if len(participants) != 2:
                parser_issues[
                    f"critical pair with {len(participants)} participant rule(s)"
                ] += 1
            else:
                rule_families[tuple(sorted(participants))] += 1
        elif "Pattern variable " in line and "can be replaced by a '_'" in line:
            category = "replaceable pattern variable"
        elif line.startswith("Warning:") or "[WARNING]" in line:
            category = "other warning"

        if category is not None:
            categories[category] += 1
            location = location_before(lines, index)
            if location is not None:
                locations[location] += 1

    return WarningInventory(
        categories=categories,
        locations=locations,
        term_heads=term_heads,
        rule_families=rule_families,
        parser_issues=parser_issues,
    )


def print_rule_families(
    title: str,
    counts: collections.Counter[tuple[str, str]],
    limit: int,
) -> None:
    if not counts:
        return
    print()
    print(title)
    for (left, right), count in counts.most_common(limit):
        print(f"{count:6d}  {left} × {right}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Summarize a warning-enabled Lambdapi check log."
    )
    parser.add_argument("log", nargs="?", help="Log path; omit or use '-' for stdin.")
    parser.add_argument(
        "--top",
        type=int,
        default=12,
        help="Maximum number of locations and critical-pair heads to show.",
    )
    parser.add_argument(
        "--strict-parse",
        action="store_true",
        help="Exit nonzero if a critical-pair block cannot be classified.",
    )
    args = parser.parse_args()

    lines = read_lines(args.log)
    inventory = warning_inventory(lines)

    total = sum(inventory.categories.values())
    print(f"Lambdapi warning summary: {total} warning(s)")
    for name, count in inventory.categories.most_common():
        print(f"{count:6d}  {name}")

    critical_pairs = inventory.categories["unjoinable critical pair"]
    if critical_pairs:
        parsed_families = sum(inventory.rule_families.values())
        print(
            "Critical-pair structure: "
            f"{sum(inventory.term_heads.values())}/{critical_pairs} term heads; "
            f"{parsed_families}/{critical_pairs} two-rule families"
        )

    print_counts(
        "Top critical-pair term heads:", inventory.term_heads, args.top
    )
    print_rule_families(
        "Top critical-pair rule families:", inventory.rule_families, args.top
    )
    print_counts("Top warning locations:", inventory.locations, args.top)

    if inventory.parser_issues:
        print_counts(
            "Critical-pair parser issues:", inventory.parser_issues, args.top
        )

    if total == 0:
        print()
        print("No recognized warning markers were found.")
    if args.strict_parse and inventory.parser_issues:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
