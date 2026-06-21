#!/usr/bin/env python3
from __future__ import annotations

import argparse
import collections
import re
import sys
from pathlib import Path


LOCATION_RE = re.compile(r"\[([^:\]]+\.lp):([0-9]+)(?::[0-9]+)?")
HEAD_RE = re.compile(r"^t ≔ @?([^\s(]+)")


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
    args = parser.parse_args()

    lines = read_lines(args.log)
    categories: collections.Counter[str] = collections.Counter()
    locations: collections.Counter[str] = collections.Counter()
    heads: collections.Counter[str] = collections.Counter()

    for index, line in enumerate(lines):
        category: str | None = None
        if line == "Unjoinable critical pair:":
            category = "unjoinable critical pair"
            for candidate in lines[index + 1 : index + 5]:
                match = HEAD_RE.match(candidate)
                if match:
                    heads[match.group(1)] += 1
                    break
        elif "Pattern variable " in line and "can be replaced by a '_'" in line:
            category = "replaceable pattern variable"
        elif line.startswith("Warning:") or "[WARNING]" in line:
            category = "other warning"

        if category is not None:
            categories[category] += 1
            location = location_before(lines, index)
            if location is not None:
                locations[location] += 1

    total = sum(categories.values())
    print(f"Lambdapi warning summary: {total} warning(s)")
    for name, count in categories.most_common():
        print(f"{count:6d}  {name}")

    print_counts("Top critical-pair term heads:", heads, args.top)
    print_counts("Top warning locations:", locations, args.top)

    if total == 0:
        print()
        print("No recognized warning markers were found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
