#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE_CHECK_FILES = [Path("emdash3_2.lp"), Path("emdash3_2_checks.lp")]
EXAMPLES_DIR = ROOT / "examples"


@dataclass
class CheckResult:
    file: str
    returncode: int | None
    duration_s: float | None


def run_command(cmd: list[str], timeout_value: str | None = None) -> tuple[int, str, float]:
    full_cmd = cmd
    if timeout_value and shutil.which("timeout"):
        full_cmd = ["timeout", "--signal=INT", timeout_value, *cmd]

    start = time.perf_counter()
    proc = subprocess.run(
        full_cmd,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    duration = time.perf_counter() - start
    return proc.returncode, proc.stdout, duration


def lambdapi_version() -> str:
    try:
        proc = subprocess.run(
            ["lambdapi", "--version"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except FileNotFoundError:
        return "not found"
    return " ".join(proc.stdout.strip().split()) or f"exit {proc.returncode}"


def check_files() -> list[Path]:
    examples = sorted(path.relative_to(ROOT) for path in EXAMPLES_DIR.glob("*.lp"))
    return [*CORE_CHECK_FILES, *examples]


def count_lines(path: Path) -> dict[str, int | dict[str, int]]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    counts: dict[str, int | dict[str, int]] = {
        "lines": len(lines),
        "nonblank_lines": sum(1 for line in lines if line.strip()),
        "comment_lines": sum(1 for line in lines if line.lstrip().startswith("//")),
        "symbols": 0,
        "rules": 0,
        "unif_rules": 0,
        "asserts": 0,
        "todos": 0,
        "deferred_mentions": 0,
        "sections": {},
    }

    symbol_re = re.compile(
        r"^\s*(?:(?:injective|constant|sequential|opaque)\s+)*symbol\b"
    )
    rule_re = re.compile(r"^\s*rule\b")
    unif_rule_re = re.compile(r"^\s*unif_rule\b")
    assert_re = re.compile(r"^\s*assert\b")
    section_re = re.compile(r"^//\s+([0-9]+)\.\s+(.*\S)\s*$")

    section_starts: list[tuple[int, str]] = []
    for i, line in enumerate(lines, start=1):
        if symbol_re.match(line):
            counts["symbols"] = int(counts["symbols"]) + 1
        if rule_re.match(line):
            counts["rules"] = int(counts["rules"]) + 1
        if unif_rule_re.match(line):
            counts["unif_rules"] = int(counts["unif_rules"]) + 1
        if assert_re.match(line):
            counts["asserts"] = int(counts["asserts"]) + 1
        if "TODO" in line:
            counts["todos"] = int(counts["todos"]) + 1
        if "deferred" in line.lower():
            counts["deferred_mentions"] = int(counts["deferred_mentions"]) + 1
        m = section_re.match(line)
        if m:
            section_starts.append((i, f"{m.group(1)}. {m.group(2)}"))

    sections: dict[str, int] = {}
    for idx, (start, name) in enumerate(section_starts):
        end = section_starts[idx + 1][0] - 1 if idx + 1 < len(section_starts) else len(lines)
        sections[name] = end - start + 1
    counts["sections"] = sections
    return counts


def run_checks(files: list[Path], timeout_value: str) -> tuple[list[CheckResult], int]:
    results: list[CheckResult] = []
    overall = 0
    for rel in files:
        cmd = ["lambdapi", "check", "-w", str(rel)]
        rc, output, duration = run_command(cmd, timeout_value)
        results.append(CheckResult(str(rel), rc, duration))
        print(f"{rel}: exit {rc}, {duration:.3f}s")
        if rc != 0:
            overall = rc
            tail = "\n".join(output.splitlines()[-40:])
            print(tail, file=sys.stderr)
            break
    return results, overall


def build_payload(args: argparse.Namespace) -> tuple[dict, int]:
    timeout_value = os.environ.get("EMDASH_TYPECHECK_TIMEOUT", "60s")
    files_to_check = check_files()
    if args.no_check:
        checks = [CheckResult(str(path), None, None) for path in files_to_check]
        rc = 0
    else:
        checks, rc = run_checks(files_to_check, timeout_value)

    files = {str(path): count_lines(ROOT / path) for path in files_to_check}
    payload = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "lambdapi_version": lambdapi_version(),
        "timeout": timeout_value,
        "core_files": [str(path) for path in CORE_CHECK_FILES],
        "example_files": [str(path) for path in files_to_check if str(path).startswith("examples/")],
        "checks": [result.__dict__ for result in checks],
        "files": files,
    }
    return payload, rc


def write_log(payload: dict, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(payload, ensure_ascii=False, sort_keys=True))
        f.write("\n")


def format_report(payload: dict) -> str:
    lines = [
        "# EMDASH Health Report",
        "",
        f"Generated: {payload['generated_at']}",
        "",
        "This report is generated by `scripts/check_metrics.py`.",
        "",
        "## Environment",
        "",
        f"- Lambdapi: `{payload['lambdapi_version']}`",
        f"- Timeout: `{payload['timeout']}`",
        "",
        "## Typecheck Timings",
        "",
        "| File | Exit | Seconds |",
        "| --- | ---: | ---: |",
    ]
    for check in payload["checks"]:
        duration = check["duration_s"]
        duration_text = "" if duration is None else f"{duration:.3f}"
        exit_text = "" if check["returncode"] is None else str(check["returncode"])
        lines.append(f"| `{check['file']}` | {exit_text} | {duration_text} |")

    lines.extend([
        "",
        "## Source Metrics",
        "",
        "| File | Lines | Symbols | Rules | Unif Rules | Asserts | TODO | Deferred |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ])
    for file_name, counts in payload["files"].items():
        lines.append(
            f"| `{file_name}` | {counts['lines']} | {counts['symbols']} | "
            f"{counts['rules']} | {counts['unif_rules']} | {counts['asserts']} | "
            f"{counts['todos']} | {counts['deferred_mentions']} |"
        )

    example_files = payload.get("example_files", [])
    if example_files:
        durations = {
            check["file"]: check["duration_s"]
            for check in payload["checks"]
            if check["file"] in example_files
        }
        exits = {
            check["file"]: check["returncode"]
            for check in payload["checks"]
            if check["file"] in example_files
        }
        lines.extend([
            "",
            "## Reviewer Milestone Examples",
            "",
            "| Example | Exit | Seconds | Lines | Asserts |",
            "| --- | ---: | ---: | ---: | ---: |",
        ])
        for file_name in example_files:
            counts = payload["files"][file_name]
            duration = durations.get(file_name)
            duration_text = "" if duration is None else f"{duration:.3f}"
            exit_value = exits.get(file_name)
            exit_text = "" if exit_value is None else str(exit_value)
            lines.append(
                f"| `{file_name}` | {exit_text} | {duration_text} | "
                f"{counts['lines']} | {counts['asserts']} |"
            )

    main_sections = payload["files"].get("emdash3_2.lp", {}).get("sections", {})
    if main_sections:
        lines.extend([
            "",
            "## `emdash3_2.lp` Section Sizes",
            "",
            "| Section | Lines |",
            "| --- | ---: |",
        ])
        for section, size in main_sections.items():
            lines.append(f"| {section} | {size} |")

    lines.append("")
    return "\n".join(lines)


def format_brief(payload: dict, rc: int) -> str:
    checks = payload["checks"]
    checked = [check for check in checks if check["returncode"] is not None]
    if not checked:
        return (
            f"source metrics collected: {len(payload['files'])} file(s); "
            "Lambdapi checks skipped"
        )
    total_s = sum(check["duration_s"] or 0 for check in checked)
    failed = [check for check in checked if check["returncode"] != 0]
    status = "passed" if rc == 0 else "failed"
    lines = [
        f"check metrics {status}: {len(checked)} file(s), {total_s:.3f}s total",
    ]
    if failed:
        lines.append("failed files:")
        for check in failed:
            lines.append(f"- {check['file']}: exit {check['returncode']}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Collect EMDASH typecheck and source-health metrics."
    )
    parser.add_argument(
        "--no-check",
        action="store_true",
        help="Collect source metrics without running Lambdapi checks.",
    )
    parser.add_argument(
        "--update-log",
        action="store_true",
        help="Append JSON metrics to logs/check-metrics.jsonl.",
    )
    parser.add_argument(
        "--write-report",
        action="store_true",
        help="Write reports/REPORT_EMDASH_HEALTH.md.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print JSON instead of the markdown summary.",
    )
    parser.add_argument(
        "--brief",
        action="store_true",
        help="Print only a compact summary after per-file check timings.",
    )
    args = parser.parse_args()

    payload, rc = build_payload(args)

    if args.update_log:
        write_log(payload, ROOT / "logs" / "check-metrics.jsonl")
    if args.write_report:
        (ROOT / "reports" / "REPORT_EMDASH_HEALTH.md").write_text(
            format_report(payload),
            encoding="utf-8",
        )

    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    elif args.brief:
        print(format_brief(payload, rc))
    else:
        print(format_report(payload))
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
