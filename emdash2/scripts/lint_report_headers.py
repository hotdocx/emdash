#!/usr/bin/env python3
"""Validate report-plan provenance headers and lifecycle registration."""

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

LIFECYCLE_SECTIONS = {
    "Active Plans": "active",
    "Completed Current-Architecture Ledgers": "completed",
    "Deferred Proposals": "deferred",
    "Superseded Or Historical Plans": "superseded",
}


def section_body(index_text: str, heading: str) -> str | None:
    match = re.search(
        rf"^## {re.escape(heading)}\n(?P<body>.*?)(?=^## |\Z)",
        index_text,
        re.M | re.S,
    )
    return None if match is None else match.group("body")


def lifecycle_entries(index_text: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for heading, lifecycle in LIFECYCLE_SECTIONS.items():
        body = section_body(index_text, heading)
        if body is None:
            result[lifecycle] = []
            continue
        result[lifecycle] = re.findall(r"^- `([^`]+\.md)`:", body, re.M)
    return result


def header_fields(path: Path) -> dict[str, str]:
    """Read top-level header fields, including wrapped continuation lines."""

    lines = path.read_text(encoding="utf-8").splitlines()[:80]
    fields: dict[str, str] = {}
    current: str | None = None
    for line in lines:
        match = re.match(r"^([A-Za-z][A-Za-z-]*):\s*(.*)$", line)
        if match is not None:
            current = match.group(1)
            fields[current] = match.group(2).strip()
            continue
        if not line.strip() or line.startswith("#"):
            current = None
            continue
        if current is not None:
            fields[current] = f"{fields[current]} {line.strip()}".strip()
    return fields


def lifecycle_status_issue(lifecycle: str, status: str) -> str | None:
    normalized = status.strip().lower().replace("**", "")
    decisive_complete = re.match(r"^(complete|completed|implemented)\b", normalized)

    if lifecycle == "active":
        if decisive_complete or "reopen only" in normalized:
            return "completed/closed status is registered under Active Plans"
        if "supersed" in normalized:
            return "superseded status is registered under Active Plans"
    elif lifecycle == "completed":
        if not re.search(r"\b(complete|completed|implemented)\b", normalized):
            return "Completed Current-Architecture Ledgers entry lacks completed status"
    elif lifecycle == "deferred":
        if not re.search(r"\b(proposed|deferred)\b", normalized):
            return "Deferred Proposals entry lacks proposed/deferred status"
    elif lifecycle == "superseded":
        if "supersed" not in normalized and "historical" not in normalized:
            return "Superseded Or Historical Plans entry lacks superseded/historical status"
    return None


def registry_issues(index_text: str, reports_root: Path) -> list[str]:
    issues: list[str] = []
    entries = lifecycle_entries(index_text)

    for heading in LIFECYCLE_SECTIONS:
        if section_body(index_text, heading) is None:
            issues.append(f"reports/INDEX.md is missing lifecycle section: {heading}")

    seen: dict[str, str] = {}
    for lifecycle, filenames in entries.items():
        for filename in filenames:
            previous = seen.get(filename)
            if previous is not None:
                issues.append(
                    f"{filename}: registered in both {previous} and {lifecycle} lifecycle sections"
                )
                continue
            seen[filename] = lifecycle

            path = reports_root / filename
            display = path.resolve(strict=False)
            if not path.exists():
                issues.append(f"{filename}: listed in reports/INDEX.md but missing")
                continue

            fields = header_fields(path)
            for field in REQUIRED_FIELDS:
                value = fields.get(field)
                if not value:
                    issues.append(f"{display}: missing {field}")
                    continue
                if field.startswith("Infinity-Codex") and value == "pending":
                    issues.append(f"{display}: {field} is still pending")

            status = fields.get("Status")
            if status:
                status_issue = lifecycle_status_issue(lifecycle, status)
                if status_issue:
                    issues.append(f"{filename}: {status_issue}: {status}")
    return issues


def main() -> int:
    index_text = INDEX.read_text(encoding="utf-8")
    issues = registry_issues(index_text, REPORTS_ROOT)
    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1

    counts = lifecycle_entries(index_text)
    rendered = ", ".join(
        f"{lifecycle}={len(counts[lifecycle])}"
        for lifecycle in ("active", "completed", "deferred", "superseded")
    )
    print(f"report lifecycle/header lint passed: {rendered}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
