#!/usr/bin/env python3
"""Execute an explicit registry suite using the shared per-target dispatch."""
from __future__ import annotations

import argparse
import os
from pathlib import Path

if __package__:
    from .check_metrics import run_checks
    from .check_registry import ROOT, inventory_issues, load_registry
else:
    from check_metrics import run_checks
    from check_registry import ROOT, inventory_issues, load_registry


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=("check", "reviewers", "all"), default="check")
    parser.add_argument("targets", nargs="*", type=Path)
    args = parser.parse_args()
    data = load_registry()
    issues = inventory_issues(data)
    if issues:
        parser.error("; ".join(issues))
    known = set(data["core"] + data["reviewers"])
    if any(str(path) not in known for path in args.targets):
        parser.error("unknown registered target; use scripts/probe.sh for temporary probes")
    names = data["core"] + data["reviewers"] if args.suite == "all" else data[args.suite]
    files = args.targets or [Path(name) for name in names]
    _, status = run_checks(files, os.environ.get("EMDASH_TYPECHECK_TIMEOUT", "90s"), prioritize=False)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
