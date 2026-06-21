#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


def read_input(path: str | None) -> list[str]:
    if path is None or path == "-":
        text = sys.stdin.read()
    else:
        text = Path(path).read_text(encoding="utf-8", errors="replace")
    return [ANSI_RE.sub("", line) for line in text.splitlines()]


def source_path(raw: str) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return ROOT / path


def find_location(lines: list[str], start: int) -> tuple[Path, int] | None:
    patterns = (
        re.compile(r'File "([^"]+)", line ([0-9]+)'),
        re.compile(r"\[?([^:\s\[\]]+\.lp):([0-9]+)(?::[0-9]+)?"),
    )
    nearby = [
        *range(start, max(-1, start - 6), -1),
        *range(start + 1, min(len(lines), start + 6)),
    ]
    for i in nearby:
        for pattern in patterns:
            match = pattern.search(lines[i])
            if match:
                return source_path(match.group(1)), int(match.group(2))
    return None


def first_error(lines: list[str]) -> int | None:
    error_words = ("[ERROR]", "Error:", "Fatal error", "Uncaught exception")
    for i, line in enumerate(lines):
        if any(word in line for word in error_words):
            return i
    for i, line in enumerate(lines):
        if "error" in line.lower():
            return i
    return None


def first_warning(lines: list[str]) -> int | None:
    warning_markers = (
        "Unjoinable critical pair:",
        "Warning:",
        "[WARNING]",
    )
    for i, line in enumerate(lines):
        if any(marker in line for marker in warning_markers):
            return i
    return None


def source_context(path: Path, line_no: int, radius: int) -> list[str]:
    if not path.exists():
        return [f"(source file not found: {path})"]
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    start = max(1, line_no - radius)
    end = min(len(lines), line_no + radius)
    width = len(str(end))
    out: list[str] = []
    for current in range(start, end + 1):
        marker = ">" if current == line_no else " "
        out.append(f"{marker} {current:{width}d}: {lines[current - 1]}")
    return out


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract a compact first-error summary from Lambdapi output."
    )
    parser.add_argument(
        "log",
        nargs="?",
        help="Log file to inspect; omit or use '-' to read stdin.",
    )
    parser.add_argument(
        "--context",
        type=int,
        default=4,
        help="Source context lines to show around the detected location.",
    )
    parser.add_argument(
        "--log-lines",
        type=int,
        default=16,
        help="Log lines to show from the first detected error.",
    )
    parser.add_argument(
        "--warning",
        action="store_true",
        help="Show the first Lambdapi warning instead of searching for an error.",
    )
    args = parser.parse_args()

    lines = read_input(args.log)
    if not lines:
        print("No log content.")
        return 1

    err = first_warning(lines) if args.warning else first_error(lines)
    if err is None:
        kind = "warning" if args.warning else "error"
        print(f"No Lambdapi {kind} marker found.")
        tail = lines[-args.log_lines :]
        if tail:
            print()
            print("## Log tail")
            for line in tail:
                print(line)
        return 1

    kind = "warning" if args.warning else "error"
    print(f"## First Lambdapi {kind}")
    for line in lines[err : min(len(lines), err + args.log_lines)]:
        print(line)

    location = find_location(lines, err)
    if location is not None:
        path, line_no = location
        print()
        print(f"## Source context: {path}:{line_no}")
        for line in source_context(path, line_no, args.context):
            print(line)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
