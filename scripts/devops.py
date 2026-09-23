#!/usr/bin/env python3
"""Shared local/CI gate selection, execution receipts and source-owned status."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import time
from urllib.parse import unquote, urlsplit
import uuid

ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "devops/gates.json"


def contract() -> dict:
    data = json.loads(CONTRACT.read_text())
    if data.get("version") != 1 or data.get("unknownPolicy") != "all-gates":
        raise ValueError("unsupported DevOps contract")
    for name, gate in data["gates"].items():
        if not re.fullmatch(r"[a-z][a-z-]+", name) or not 1 <= gate["timeoutSeconds"] <= 21600:
            raise ValueError("invalid gate identity or deadline")
        if not gate["commands"]:
            raise ValueError(f"required gate has no commands: {name}")
        for command in gate["commands"]:
            if not command or not all(isinstance(arg, str) and arg for arg in command):
                raise ValueError(f"invalid command in {name}")
    for rule in data["rules"]:
        if not set(rule["gates"]) <= set(data["gates"]):
            raise ValueError("rule names unknown gate")
    return data


def matches(path: str, pattern: str) -> bool:
    if pattern.endswith("/**"):
        return path.startswith(pattern[:-2])
    # Root patterns must not accidentally match a basename at any depth.
    if "/" not in pattern and "/" in path:
        return False
    return PurePosixPath(path).match(pattern)


def select_gates(paths: list[str], data: dict | None = None, *, full: bool = False) -> dict:
    data = data or contract()
    policy_changes = [path for path in paths if any(matches(path, pattern) for pattern in data.get("fullValidationPaths", []))]
    full = full or bool(policy_changes)
    selected: dict[str, list[str]] = {}
    if full:
        reason = ["validation policy changed: " + path for path in policy_changes] or ["explicit full selection"]
        selected = {name: list(reason) for name in data["gates"]}
    for path in paths:
        matched = False
        for rule in data["rules"]:
            if any(matches(path, pattern) for pattern in rule["paths"]):
                matched = True
                for name in rule["gates"]:
                    selected.setdefault(name, []).append(path)
        if any(path.startswith(prefix) for prefix in data["semanticTypeScriptPrefixes"]) and path not in data["semanticTypeScriptExclusions"]:
            for name in ("conformance", "scale-conformance"):
                selected.setdefault(name, []).append(path)
        if not matched:
            for name in data["gates"]:
                selected.setdefault(name, []).append(f"unclassified path: {path}")
    selected.setdefault("docs", ["diff and changed-document hygiene"])
    for owner, covered in data["dominates"].items():
        if owner in selected:
            for name in covered:
                selected.pop(name, None)
    rows = []
    for name, gate in data["gates"].items():
        if name in selected:
            rows.append({"gate": name, **gate["requirements"],
                         "minutes": math.ceil(gate["timeoutSeconds"] / 60) + 10,
                         "reasons": sorted(set(selected[name]))})
    # GitHub limits each job to six hours; setup time is inside that ceiling.
    for row in rows:
        row["minutes"] = min(360, row["minutes"])
    return {"schema": "emdash-gate-plan-v1", "paths": sorted(set(paths)), "include": rows}


def revision(name: str) -> str:
    return subprocess.check_output(["git", "rev-parse", "--verify", "--end-of-options", name + "^{commit}"],
                                   cwd=ROOT, text=True, stderr=subprocess.PIPE).strip()


def changed_paths(base: str | None, head: str = "HEAD") -> list[str]:
    if base and set(base) != {"0"}:
        arguments = ["git", "diff", "--no-renames", "--name-only", "-z", revision(base), revision(head), "--"]
        paths = set(subprocess.check_output(arguments, cwd=ROOT).decode().split("\0")) - {""}
        if revision(head) == revision("HEAD"):
            paths.update(changed_paths(None))
        return sorted(paths)
    if base:
        arguments = ["git", "ls-files", "-z"]
        return sorted(set(subprocess.check_output(arguments, cwd=ROOT).decode().split("\0")) - {""})
    changed = subprocess.check_output(["git", "diff", "--no-renames", "--name-only", "-z", "HEAD", "--"], cwd=ROOT)
    untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "-z"], cwd=ROOT)
    return sorted(set((changed + untracked).decode().split("\0")) - {""})


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gate_inputs(gate: dict) -> dict[str, str]:
    names = subprocess.check_output(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT).decode().split("\0")
    return {name: digest(ROOT / name) for name in sorted(set(names))
            if name and (ROOT / name).is_file() and any(matches(name, pattern) for pattern in gate["inputs"])}


def markdown_links(content: str) -> list[str]:
    content = re.sub(r"^```[^\n]*\n.*?^```\s*$", "", content, flags=re.M | re.S)
    # Code is opaque, including inside link labels. A placeholder retains
    # labels such as [`owner.ts`](owner.ts) while hiding F[x](y) examples.
    content = re.sub(r"(`+).*?\1", "CODE", content, flags=re.S)
    return re.findall(r"(?<!!)\[[^\]\n]+\]\(([^\s)]+)\)", content)


def check_documents(paths: list[str]) -> int:
    if os.environ.get("EMDASH_DEVOPS_BASE"):
        subprocess.run(["git", "diff", "--check", os.environ["EMDASH_DEVOPS_BASE"],
                        os.environ["EMDASH_DEVOPS_HEAD"], "--"], cwd=ROOT, check=True)
    subprocess.run(["git", "diff", "--check"], cwd=ROOT, check=True)
    subprocess.run(["git", "diff", "--cached", "--check"], cwd=ROOT, check=True)
    issues = []
    count = 0
    for name in paths:
        path = ROOT / name
        if path.suffix != ".md" or not path.is_file():
            continue
        for target in markdown_links(path.read_text()):
            url = urlsplit(target.strip("<>"))
            if url.scheme or not url.path or url.netloc:
                continue
            resolved = path.parent / unquote(url.path)
            count += 1
            if not resolved.exists():
                issues.append(f"{name}: missing local link {target}")
    if any(name.startswith("emdash2/reports/") for name in paths):
        subprocess.run(["python3", "emdash2/scripts/lint_report_headers.py"], cwd=ROOT, check=True)
    if issues:
        print("\n".join(issues), file=sys.stderr)
        return 1
    print(f"Document hygiene passed: {count} local links in changed Markdown files.")
    return 0


def run_gate(name: str, paths: list[str]) -> dict:
    gate = contract()["gates"][name]
    inputs = gate_inputs(gate)
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex
    directory = ROOT / "emdash2/logs/devops"
    directory.mkdir(parents=True, exist_ok=True)
    log = directory / f"{name}-{run_id}.log"
    receipt_path = directory / f"{name}-{run_id}.json"
    env = dict(os.environ, EMDASH_DEVOPS_CHANGED_PATHS=json.dumps(paths))
    started = time.monotonic()
    results = []
    with log.open("x") as stream:
        for command in gate["commands"]:
            print(f"{name}: {' '.join(command)}; log {log}", flush=True)
            remaining = gate["timeoutSeconds"] - (time.monotonic() - started)
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = process.wait(timeout=max(0.001, remaining))
            except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                code = 124 if isinstance(error, subprocess.TimeoutExpired) else 130
            results.append({"command": command, "exit": code})
            if code:
                break
    stable = inputs == gate_inputs(gate)
    succeeded = len(results) == len(gate["commands"]) and all(row["exit"] == 0 for row in results)
    outcome = "passed-fresh" if succeeded and stable else "inputs-changed" if succeeded else "failed"
    if any(row["exit"] == 124 for row in results):
        outcome = "timeout"
    elif any(row["exit"] == 130 for row in results):
        outcome = "cancelled"
    receipt = {"schema": "emdash-gate-receipt-v1", "gate": name, "id": run_id,
               "revision": revision("HEAD"), "inputs": inputs, "commands": results,
               "outcome": outcome, "wallSeconds": time.monotonic() - started,
               "log": str(log.relative_to(ROOT)), "logSha256": digest(log),
               "qualification": "operational gate evidence; mathematical/profile boundaries remain"}
    with receipt_path.open("x") as stream:
        json.dump(receipt, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(f"{name}: {outcome}; receipt {receipt_path}", flush=True)
    if outcome != "passed-fresh":
        print("\n".join(log.read_text(errors="replace").splitlines()[-60:]), file=sys.stderr)
    return receipt


def doctor(formal: bool = False, printing: bool = False) -> int:
    required = ["git", "python3", "node", "bash", "timeout", "prlimit", "flock", "nice"]
    if formal:
        required += ["lambdapi", "ocamlc", "opam"]
    if printing:
        required += ["qpdf", "pdfinfo", "pdftotext", "pdffonts", "pdftoppm"]
    report = {"schema": "emdash-doctor-v1", "tools": {name: shutil.which(name) for name in required},
              "packageManager": json.loads((ROOT / "package.json").read_text())["packageManager"],
              "workspaceInstalled": (ROOT / "node_modules").is_dir(),
              "guardPolicy": "per-invocation serial guard; 2GiB/90s default; named exceptions in emdash2/checks.json",
              "bookOwners": ["emdash2/book/book.json", "emdash2/book/expansion.json", "emdash2/book/evidence.json"]}
    versions = {"python": sys.version.split()[0]}
    if report["tools"]["node"]:
        versions["node"] = subprocess.check_output(["node", "--version"], text=True, timeout=5).strip()
    report["versions"] = versions
    failed = any(path is None for path in report["tools"].values())
    if versions.get("node"):
        major, minor = map(int, versions["node"].lstrip("v").split(".")[:2])
        if (major, minor) < (22, 13):
            print("Contributor Node must be >=22.13.", file=sys.stderr)
            failed = True
    if formal and not failed:
        verified = subprocess.run(["python3", "scripts/verification-toolchain.py", "verify"], cwd=ROOT,
                                  capture_output=True, text=True, timeout=60)
        try:
            report["formalVerification"] = json.loads(verified.stdout)
        except ValueError:
            report["formalVerification"] = {"output": verified.stdout, "error": verified.stderr}
        failed = verified.returncode != 0
    print(json.dumps(report, indent=2))
    return int(failed)


def status(claim: str | None) -> None:
    records = []
    for directory in (ROOT / "emdash2/logs/check-runs", ROOT / "emdash2/logs/devops"):
        for path in sorted(directory.glob("*.json"), reverse=True):
            try:
                item = json.loads(path.read_text())
            except (OSError, ValueError):
                continue
            records.append({**item, "receipt": str(path.relative_to(ROOT))})
    if claim:
        book = json.loads((ROOT / "emdash2/book/evidence.json").read_text())
        entry = book["claims"][claim]
        reviews = []
        for reviewer in entry.get("reviewers", []):
            found = next((item for item in records if (item.get("target") == reviewer["file"]
                          or reviewer["file"] in item.get("targets", []))
                          and item.get("packageRoot") == str(ROOT / "emdash2")), None)
            reviews.append({"target": reviewer["file"], "receipt": found.get("receipt") if found else None,
                            "recordedOutcome": found.get("outcome") if found else "not-run",
                            "note": "recorded execution only; revalidate inputs/profile before reuse"})
        print(json.dumps({"claim": claim, "bookEvidence": entry, "executions": reviews}, indent=2))
    else:
        print(json.dumps({"schema": "emdash-status-v1", "recent": [
            {key: row.get(key) for key in ("id", "kind", "gate", "target", "targets", "packageRoot", "outcome", "receipt")}
            for row in sorted(records, key=lambda row: row.get("id", ""), reverse=True)[:20]],
            "note": "Historical receipts, not a fresh validation or consistency certificate."}, indent=2))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    doctor_parser = sub.add_parser("doctor")
    doctor_parser.add_argument("--formal", action="store_true")
    doctor_parser.add_argument("--print", dest="printing", action="store_true")
    for action in ("plan", "check"):
        command = sub.add_parser(action)
        command.add_argument("--base")
        command.add_argument("--head", default="HEAD")
        command.add_argument("--full", action="store_true")
        command.add_argument("--paths", nargs="*")
        if action == "plan":
            command.add_argument("--github-output", action="store_true")
        else:
            command.add_argument("--gate", choices=tuple(contract()["gates"]))
            command.add_argument("--explain", action="store_true")
    sub.add_parser("targets")
    sub.add_parser("docs")
    status_parser = sub.add_parser("status")
    status_parser.add_argument("--claim")
    args = parser.parse_args()
    if args.action == "doctor":
        return doctor(args.formal, args.printing)
    if args.action == "targets":
        return subprocess.run(["python3", "emdash2/scripts/check_registry.py", "--list", "all"], cwd=ROOT).returncode
    if args.action == "status":
        status(args.claim)
        return 0
    if args.action == "docs":
        return check_documents(json.loads(os.environ.get("EMDASH_DEVOPS_CHANGED_PATHS", "null")) or changed_paths(None))
    if args.action == "check" and revision(args.head) != revision("HEAD"):
        parser.error("check executes the current checkout; --head must resolve to HEAD")
    if args.base and set(args.base) != {"0"}:
        os.environ["EMDASH_DEVOPS_BASE"] = revision(args.base)
        os.environ["EMDASH_DEVOPS_HEAD"] = revision(args.head)
    paths = args.paths if args.paths is not None else changed_paths(args.base, args.head)
    plan = select_gates(paths, full=args.full)
    if args.action == "plan" or args.explain:
        print(json.dumps(plan, indent=2))
        if args.action == "plan" and args.github_output:
            with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
                stream.write("matrix=" + json.dumps({"include": plan["include"]}, separators=(",", ":")) + "\n")
        return 0
    names = [args.gate] if args.gate else [row["gate"] for row in plan["include"]]
    for name in names:
        if run_gate(name, paths)["outcome"] != "passed-fresh":
            return 1
    return 0


if __name__ == "__main__":
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"DevOps command failed: {error}", file=sys.stderr)
        raise SystemExit(2)
