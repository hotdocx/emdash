#!/usr/bin/env python3
"""Check active plan reports for the standard recovery/provenance header."""

from __future__ import annotations

import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
REPORTS_ROOT = REPO_ROOT / "reports"
INDEX = REPORTS_ROOT / "INDEX.md"
REQUIRED_FIELDS = [
    "Plan-ID",
    "Depends-On",
    "Supersedes",
    "Side-Task-Ledger",
    "Infinity-Codex-Origin",
    "Infinity-Codex-Decision-Responses",
    "Status",
]


def current_plan_files() -> list[Path]:
    text = INDEX.read_text(encoding="utf-8")
    match = re.search(r"^## Current Plans\n(?P<body>.*?)(?=^## )", text, re.M | re.S)
    if match is None:
        raise RuntimeError("reports/INDEX.md is missing a Current Plans section")
    body = match.group("body")
    filenames = re.findall(r"- `([^`]+\.md)`:", body)
    return [REPORTS_ROOT / filename for filename in filenames]


def header_fields(path: Path) -> dict[str, str]:
    lines = path.read_text(encoding="utf-8").splitlines()[:40]
    fields: dict[str, str] = {}
    for line in lines:
        match = re.match(r"^([A-Za-z][A-Za-z-]*):\s*(.*)$", line)
        if match is not None:
            fields[match.group(1)] = match.group(2).strip()
    return fields


def main() -> int:
    issues: list[str] = []
    for path in current_plan_files():
        if not path.exists():
            issues.append(f"{path.relative_to(REPO_ROOT)}: listed in reports/INDEX.md but missing")
            continue
        fields = header_fields(path)
        for field in REQUIRED_FIELDS:
            value = fields.get(field)
            if not value:
                issues.append(f"{path.relative_to(REPO_ROOT)}: missing {field}")
                continue
            if field.startswith("Infinity-Codex") and value == "pending":
                issues.append(f"{path.relative_to(REPO_ROOT)}: {field} is still pending")
    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1
    print(f"report header lint passed: {len(current_plan_files())} current plan(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
