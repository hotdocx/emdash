#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE_CHECK_FILES = [
    Path("emdash3_2.lp"),
    Path("emdash3_2_presheaves.lp"),
    Path("emdash3_2_fibrewise_sigma.lp"),
    Path("emdash3_2_nat_arithmetic.lp"),
    Path("emdash3_2_finite_families.lp"),
    Path("emdash3_2_finite_limits.lp"),
    Path("emdash3_2_commutative_algebra.lp"),
    Path("emdash3_2_commutative_algebra_category.lp"),
    Path("emdash3_2_commutative_algebra_product.lp"),
    Path("emdash3_2_commutative_algebra_f2.lp"),
    Path("emdash3_2_commutative_algebra_finite.lp"),
    Path("emdash3_2_commutative_algebra_polynomial.lp"),
    Path("emdash3_2_commutative_algebra_localization.lp"),
    Path("emdash3_2_commutative_algebra_laurent.lp"),
    Path("emdash3_2_commutative_algebra_localization_unit.lp"),
    Path("emdash3_2_commutative_algebra_localization_zero.lp"),
    Path("emdash3_2_commutative_algebra_localization_idempotent.lp"),
    Path("emdash3_2_commutative_algebra_localization_comparison.lp"),
    Path("emdash3_2_commutative_algebra_localization_overlap.lp"),
    Path("emdash3_2_commutative_algebra_presheaves.lp"),
    Path("emdash3_2_walking_end_hit.lp"),
    Path("emdash3_2_eq1_hom_action.lp"),
    Path("emdash3_2_eq1_evidence_property.lp"),
    Path("emdash3_2_telescope_localization_hit.lp"),
    Path("emdash3_2_sieves.lp"),
    Path("emdash3_2_sites.lp"),
    Path("emdash3_2_sieve_extensions.lp"),
    Path("emdash3_2_direct_cover_algebras.lp"),
    Path("emdash3_2_direct_cover_completion_hit.lp"),
    Path("emdash3_2_direct_cover_completion_eliminator.lp"),
    Path("emdash3_2_generated_topologies.lp"),
    Path("emdash3_2_ringed_sites.lp"),
    Path("emdash3_2_site_basis.lp"),
    Path("emdash3_2_commutative_algebra_ringed_space_covers.lp"),
    Path("emdash3_2_commutative_algebra_binary_covers.lp"),
    Path("emdash3_2_commutative_algebra_ringed_space_restrictions.lp"),
    Path("emdash3_2_commutative_algebra_locality.lp"),
    Path("emdash3_2_commutative_algebra_local_ringed_sites.lp"),
    Path("emdash3_2_commutative_algebra_matching.lp"),
    Path("emdash3_2_commutative_algebra_glue.lp"),
    Path("emdash3_2_commutative_algebra_affine_glue.lp"),
    Path("emdash3_2_commutative_algebra_zariski.lp"),
    Path("emdash3_2_commutative_algebra_zariski_topology.lp"),
    Path("emdash3_2_commutative_algebra_localization_split.lp"),
    Path("emdash3_2_commutative_algebra_affine_spec.lp"),
    Path("emdash3_2_commutative_algebra_affine_zariski.lp"),
    Path("emdash3_2_commutative_algebra_affine_ringed_sites.lp"),
    Path("emdash3_2_commutative_algebra_affine_locality.lp"),
    Path("emdash3_2_commutative_algebra_affine_schemes.lp"),
    Path("emdash3_2_commutative_algebra_affine_basis.lp"),
    Path("emdash3_2_commutative_algebra_affine_cover_charts.lp"),
    Path("emdash3_2_commutative_algebra_affine_cover_presentations.lp"),
    Path("emdash3_2_commutative_algebra_affine_cover_refinements.lp"),
    Path("emdash3_2_commutative_algebra_locally_ringed_space_presentations.lp"),
    Path("emdash3_2_commutative_algebra_site_relative_schemes.lp"),
    Path("emdash3_2_commutative_algebra_scheme_chart_overlaps.lp"),
    Path("emdash3_2_commutative_algebra_scheme_laurent_overlaps.lp"),
    Path("emdash3_2_commutative_algebra_affine_points.lp"),
    Path("emdash3_2_commutative_algebra_affine_intersections.lp"),
    Path("emdash3_2_commutative_algebra_affine_atlas.lp"),
    Path("emdash3_2_checks.lp"),
]
# Run the two consistently near-timeout aggregate targets before sustained
# sequential checking can make their measurements load/thermal sensitive.
# Results remain reported in CORE_CHECK_FILES order.
CHECK_PRIORITY_FILES = [
    Path("emdash3_2_checks.lp"),
    Path("emdash3_2_commutative_algebra_affine_glue.lp"),
]
EXAMPLES_DIR = ROOT / "examples"
HEALTH_REPORT = ROOT / "reports" / "REPORT_EMDASH_HEALTH.md"
HEALTH_STATE = ROOT / "logs" / "check-health-state.json"
HEALTH_STATE_VERSION = 1
SOURCE_METRICS_SNAPSHOT_RE = re.compile(
    r"^- Source-metrics snapshot: `sha256:(?P<digest>[0-9a-f]{64})`$", re.MULTILINE
)
CHECK_CONTENT_SNAPSHOT_RE = re.compile(
    r"^- Check-content snapshot: `sha256:(?P<digest>[0-9a-f]{64})`$", re.MULTILINE
)
DEFAULT_REGISTERED_TIMEOUT = "90s"


@dataclass
class CheckResult:
    file: str
    returncode: int | None
    duration_s: float | None
    evidence: str = "current"


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


def lambdapi_check_command(path: Path) -> list[str]:
    warnings = os.environ.get("EMDASH_LAMBDAPI_WARNINGS", "0").lower()
    if warnings in {"1", "true", "yes", "on"}:
        warning_flags: list[str] = []
    elif warnings in {"0", "false", "no", "off"}:
        warning_flags = ["-w"]
    else:
        raise ValueError(f"invalid EMDASH_LAMBDAPI_WARNINGS value: {warnings}")

    extra_flags = shlex.split(os.environ.get("EMDASH_LAMBDAPI_FLAGS", ""))
    return ["lambdapi", "check", *warning_flags, *extra_flags, str(path)]


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
        r"^\s*(?:(?:injective|constant|sequential|opaque|private|protected)\s+)*symbol\b"
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


def source_metrics_snapshot(files: dict[str, dict]) -> str:
    """Hash only the stable source-metric payload, excluding timings/date."""
    canonical = json.dumps(
        files,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def check_content_snapshot(files: list[Path], root: Path = ROOT) -> str:
    """Hash exact checked file paths and bytes for resumable evidence."""
    digest = hashlib.sha256()
    for path in sorted(files, key=str):
        digest.update(str(path).encode("utf-8"))
        digest.update(b"\0")
        digest.update((root / path).read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def report_source_metrics_snapshot(report: str) -> str | None:
    match = SOURCE_METRICS_SNAPSHOT_RE.search(report)
    return None if match is None else match.group("digest")


def report_check_content_snapshot(report: str) -> str | None:
    match = CHECK_CONTENT_SNAPSHOT_RE.search(report)
    return None if match is None else match.group("digest")


def report_snapshot_issue(
    expected: str,
    report: str,
    expected_content: str | None = None,
) -> str | None:
    actual_metrics = report_source_metrics_snapshot(report)
    if actual_metrics is None:
        return "health report has no source-metrics snapshot"
    if actual_metrics != expected:
        return (
            "health report source metrics are stale: "
            f"recorded sha256:{actual_metrics}, current sha256:{expected}"
        )
    if expected_content is not None:
        actual_content = report_check_content_snapshot(report)
        if actual_content is None:
            return "health report has no check-content snapshot"
        if actual_content != expected_content:
            return (
                "health report checked contents are stale: "
                f"recorded sha256:{actual_content}, "
                f"current sha256:{expected_content}"
            )
    return None


def check_state_identity(
    files: list[Path],
    content_snapshot: str,
    version: str,
    timeout_value: str,
) -> dict[str, object]:
    return {
        "state_version": HEALTH_STATE_VERSION,
        "files": [str(path) for path in files],
        "content_snapshot": content_snapshot,
        "lambdapi_version": version,
        "timeout": timeout_value,
        "warnings_enabled": os.environ.get("EMDASH_LAMBDAPI_WARNINGS", "0").lower()
        in {"1", "true", "yes", "on"},
        "extra_lambdapi_flags": os.environ.get("EMDASH_LAMBDAPI_FLAGS", ""),
    }


def load_resume_checks(path: Path, identity: dict[str, object]) -> dict[str, CheckResult]:
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}
    if state.get("identity") != identity:
        return {}
    checks: dict[str, CheckResult] = {}
    for file_name, item in state.get("checks", {}).items():
        if item.get("returncode") == 0:
            checks[file_name] = CheckResult(
                file=file_name,
                returncode=0,
                duration_s=item.get("duration_s"),
                evidence="resumed",
            )
    return checks


def write_resume_checks(
    path: Path,
    identity: dict[str, object],
    checks: dict[str, CheckResult],
) -> None:
    successful = {
        file_name: {
            "returncode": 0,
            "duration_s": result.duration_s,
        }
        for file_name, result in checks.items()
        if result.returncode == 0
    }
    state = {
        "identity": identity,
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "checks": successful,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(state, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def check_execution_order(files: list[Path]) -> list[Path]:
    prioritized = [path for path in CHECK_PRIORITY_FILES if path in files]
    return [*prioritized, *(path for path in files if path not in prioritized)]


def run_checks(
    files: list[Path],
    timeout_value: str,
    resumed: dict[str, CheckResult] | None = None,
    continue_after_failure: bool = False,
    save_success: Callable[[dict[str, CheckResult]], None] | None = None,
) -> tuple[list[CheckResult], int]:
    results_by_file: dict[str, CheckResult] = dict(resumed or {})
    overall = 0
    for rel in check_execution_order(files):
        if str(rel) in results_by_file and results_by_file[str(rel)].returncode == 0:
            duration = results_by_file[str(rel)].duration_s
            duration_text = "unknown" if duration is None else f"{duration:.3f}s"
            print(f"{rel}: resumed exit 0, {duration_text}")
            continue
        cmd = lambdapi_check_command(rel)
        rc, output, duration = run_command(cmd, timeout_value)
        results_by_file[str(rel)] = CheckResult(str(rel), rc, duration)
        print(f"{rel}: exit {rc}, {duration:.3f}s")
        if rc == 0 and save_success is not None:
            save_success(results_by_file)
        elif rc != 0:
            overall = overall or rc
            tail = "\n".join(output.splitlines()[-40:])
            print(tail, file=sys.stderr)
            if not continue_after_failure:
                break
    results = [results_by_file[str(path)] for path in files if str(path) in results_by_file]
    if len(results) != len(files):
        overall = overall or 1
    return results, overall


def build_payload(args: argparse.Namespace) -> tuple[dict, int]:
    timeout_value = os.environ.get(
        "EMDASH_TYPECHECK_TIMEOUT", DEFAULT_REGISTERED_TIMEOUT
    )
    files_to_check = check_files()
    files = {str(path): count_lines(ROOT / path) for path in files_to_check}
    content_snapshot = check_content_snapshot(files_to_check)
    version = lambdapi_version()
    identity = check_state_identity(
        files_to_check,
        content_snapshot,
        version,
        timeout_value,
    )
    if args.no_check:
        checks = [CheckResult(str(path), None, None) for path in files_to_check]
        rc = 0
    elif args.resume:
        resumed = load_resume_checks(HEALTH_STATE, identity)

        def save_success(results: dict[str, CheckResult]) -> None:
            write_resume_checks(HEALTH_STATE, identity, results)

        checks, rc = run_checks(
            files_to_check,
            timeout_value,
            resumed=resumed,
            continue_after_failure=True,
            save_success=save_success,
        )
    else:
        checks, rc = run_checks(files_to_check, timeout_value)

    payload = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "lambdapi_version": version,
        "timeout": timeout_value,
        "warnings_enabled": os.environ.get(
            "EMDASH_LAMBDAPI_WARNINGS", "0"
        ).lower()
        in {"1", "true", "yes", "on"},
        "extra_lambdapi_flags": os.environ.get("EMDASH_LAMBDAPI_FLAGS", ""),
        "core_files": [str(path) for path in CORE_CHECK_FILES],
        "example_files": [str(path) for path in files_to_check if str(path).startswith("examples/")],
        "checks": [result.__dict__ for result in checks],
        "files": files,
        "source_metrics_snapshot": source_metrics_snapshot(files),
        "check_content_snapshot": content_snapshot,
        "resume_enabled": args.resume,
        "resumed_check_count": sum(
            1 for result in checks if result.evidence == "resumed"
        ),
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
        f"- Warnings enabled: `{payload['warnings_enabled']}`",
        f"- Extra Lambdapi flags: `{payload['extra_lambdapi_flags']}`",
        f"- Source-metrics snapshot: `sha256:{payload['source_metrics_snapshot']}`",
        f"- Check-content snapshot: `sha256:{payload['check_content_snapshot']}`",
        f"- Resumable evidence: `{payload.get('resume_enabled', False)}`",
        f"- Resumed successful checks: `{payload.get('resumed_check_count', 0)}`",
        "",
        "## Typecheck Timings",
        "",
        "| File | Exit | Seconds | Evidence |",
        "| --- | ---: | ---: | --- |",
    ]
    for check in payload["checks"]:
        duration = check["duration_s"]
        duration_text = "" if duration is None else f"{duration:.3f}"
        exit_text = "" if check["returncode"] is None else str(check["returncode"])
        evidence = check.get("evidence", "current")
        lines.append(
            f"| `{check['file']}` | {exit_text} | {duration_text} | {evidence} |"
        )

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
    resumed = sum(1 for check in checked if check.get("evidence") == "resumed")
    if resumed:
        lines.append(f"resumed exact-snapshot successes: {resumed}")
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
        "--resume",
        action="store_true",
        help=(
            "Reuse only exit-0 evidence with the exact checked-content and "
            "environment identity; continue after failures and retain progress."
        ),
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
        "--check-report",
        action="store_true",
        help="Fail if the health report's stable source metrics are stale.",
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

    if args.no_check and args.resume:
        parser.error("--no-check and --resume cannot be combined")

    payload, rc = build_payload(args)

    report_rc = 0
    if args.check_report:
        if not HEALTH_REPORT.exists():
            print(
                f"{HEALTH_REPORT.relative_to(ROOT)}: health report is missing",
                file=sys.stderr,
            )
            report_rc = 1
        else:
            issue = report_snapshot_issue(
                payload["source_metrics_snapshot"],
                HEALTH_REPORT.read_text(encoding="utf-8"),
                payload["check_content_snapshot"],
            )
            if issue is None:
                print(
                    "health source-metrics snapshot check passed: "
                    f"sha256:{payload['source_metrics_snapshot']}"
                )
            else:
                print(
                    f"{HEALTH_REPORT.relative_to(ROOT)}: {issue}; run `make health`",
                    file=sys.stderr,
                )
                report_rc = 1

    if args.update_log:
        write_log(payload, ROOT / "logs" / "check-metrics.jsonl")
    if args.write_report and (rc == 0 or args.no_check):
        HEALTH_REPORT.write_text(
            format_report(payload),
            encoding="utf-8",
        )
    elif args.write_report:
        print(
            f"{HEALTH_REPORT.relative_to(ROOT)}: not updated because checks failed",
            file=sys.stderr,
        )

    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    elif args.brief:
        print(format_brief(payload, rc))
    else:
        print(format_report(payload))
    return rc or report_rc


if __name__ == "__main__":
    raise SystemExit(main())
