#!/usr/bin/env python3
"""Verify emdash3_2.lp's heading structure and mirrored header map."""

from __future__ import annotations

import difflib
import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE = REPO_ROOT / "emdash3_2.lp"
TOC_START = "  Table of contents / source section map:"
TOC_END = "  Grouped architecture map:"
TOC_ENTRY = re.compile(r"^\s+(?P<id>[0-9]+[a-z]?)\. (?P<title>\S.*)$")
SOURCE_ENTRY = re.compile(r"^// (?P<id>[0-9]+[a-z]?)\. (?P<title>\S.*)$")
HEADING_ID = re.compile(r"^(?P<section>[0-9]+)(?P<suffix>[a-z]?)$")

# Section 18z is an intentional terminal bridge for rules whose owners cross
# earlier section boundaries. Any new nonsequential suffix requires an
# explicit architectural decision here instead of silently creating a gap.
RESERVED_TERMINAL_SUBSECTIONS = {"18z"}


def entries(lines: list[str], pattern: re.Pattern[str]) -> list[tuple[str, str]]:
    result: list[tuple[str, str]] = []
    for line in lines:
        match = pattern.match(line)
        if match is not None:
            result.append((match.group("id"), match.group("title")))
    return result


def display(items: list[tuple[str, str]]) -> list[str]:
    return [f"{identifier}. {title}" for identifier, title in items]


def heading_structure_issues(items: list[tuple[str, str]]) -> list[str]:
    """Return ordering/parent/sequence issues for formal source headings."""
    issues: list[str] = []
    current_section: int | None = None
    expected_suffix = "a"
    terminal_subsection_seen = False

    for identifier, _ in items:
        match = HEADING_ID.fullmatch(identifier)
        if match is None:
            issues.append(f"invalid heading identifier {identifier!r}")
            continue

        section = int(match.group("section"))
        suffix = match.group("suffix")
        if not suffix:
            current_section = section
            expected_suffix = "a"
            terminal_subsection_seen = False
            continue

        if current_section != section:
            issues.append(
                f"subsection {identifier} is under section {current_section}, "
                f"expected parent section {section}"
            )
            continue

        if identifier in RESERVED_TERMINAL_SUBSECTIONS:
            terminal_subsection_seen = True
            continue

        if terminal_subsection_seen:
            issues.append(
                f"subsection {identifier} follows reserved terminal subsection"
            )
            continue

        if suffix != expected_suffix:
            issues.append(
                f"subsection {identifier} is nonsequential; "
                f"expected {section}{expected_suffix}"
            )
            expected_suffix = chr(ord(suffix) + 1)
            continue

        expected_suffix = chr(ord(expected_suffix) + 1)

    return issues


def main() -> int:
    lines = SOURCE.read_text(encoding="utf-8").splitlines()
    try:
        start = lines.index(TOC_START) + 1
        end = lines.index(TOC_END, start)
    except ValueError as error:
        print(f"{SOURCE.relative_to(REPO_ROOT)}: missing source-map marker: {error}", file=sys.stderr)
        return 1

    toc = entries(lines[start:end], TOC_ENTRY)
    source = entries(lines[end + 1 :], SOURCE_ENTRY)

    identifiers = [identifier for identifier, _ in source]
    if len(identifiers) != len(set(identifiers)):
        print(f"{SOURCE.relative_to(REPO_ROOT)}: duplicate formal heading identifier", file=sys.stderr)
        return 1

    top_level = [int(identifier) for identifier in identifiers if identifier.isdigit()]
    if top_level != list(range(21)):
        print(
            f"{SOURCE.relative_to(REPO_ROOT)}: top-level sections are {top_level}, expected 0..20",
            file=sys.stderr,
        )
        return 1

    structure_issues = heading_structure_issues(source)
    if structure_issues:
        for issue in structure_issues:
            print(f"{SOURCE.relative_to(REPO_ROOT)}: {issue}", file=sys.stderr)
        return 1

    if toc != source:
        print(
            f"{SOURCE.relative_to(REPO_ROOT)}: header source map differs from formal headings",
            file=sys.stderr,
        )
        for line in difflib.unified_diff(
            display(toc),
            display(source),
            fromfile="header map",
            tofile="source headings",
            lineterm="",
        ):
            print(line, file=sys.stderr)
        return 1

    print(
        f"source TOC check passed: {len(source)} heading(s), sections 0-20, "
        "subsections sequential"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
