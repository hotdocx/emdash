#!/usr/bin/env python3
"""Validate workflow provenance and bind a Pages bundle to its checked bytes."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess


def qualified_run(run: dict, repository: str, *, manual: bool = True) -> bool:
    return (
        run.get("status") == "completed" and run.get("conclusion") == "success"
        and run.get("event") in ({"push", "workflow_dispatch"} if manual else {"push"})
        and run.get("head_branch") == "main"
        and (run.get("head_repository") or {}).get("full_name") == repository
        and run.get("path") == ".github/workflows/validate.yml"
        and re.fullmatch(r"[0-9a-f]{40}", run.get("head_sha", "")) is not None
        and type(run.get("id")) is int and run["id"] > 0
        and type(run.get("run_attempt")) is int and run["run_attempt"] > 0
    )


def qualified_base(runs: list[dict], repository: str, current: str) -> str | None:
    candidates = [run for run in runs if qualified_run(run, repository) and run["head_sha"] != current]
    return max(candidates, key=lambda run: run["id"])["head_sha"] if candidates else None


def select_artifact(run: dict, artifacts: list[dict], repository: str, *, manual: bool = False) -> dict:
    if not qualified_run(run, repository, manual=manual):
        raise ValueError("deployment requires a successful main validation from this repository")
    name = "reviewer-dist-" + str(run["run_attempt"])
    matches = [item for item in artifacts if item.get("name") == name and not item.get("expired")]
    if len(matches) > 1:
        raise ValueError("ambiguous validation artifact")
    if not matches and manual:
        raise ValueError("this validation run has no retained reviewer artifact; run full validation first")
    return {"deploy": bool(matches), "artifact": name, "sha": run["head_sha"],
            "run": str(run["id"]), "attempt": str(run["run_attempt"])}


def bundle_files(directory: Path) -> dict[str, str]:
    result = {}
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            raise ValueError("Pages artifacts must not contain symlinks")
        if path.is_file() and path != directory / "validation.json":
            result[path.relative_to(directory).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    if "index.html" not in result:
        raise ValueError("reviewer artifact has no index.html")
    return result


def write_manifest(directory: Path, sha: str, run: str, attempt: str) -> None:
    if not re.fullmatch(r"[0-9a-f]{40}", sha) or not run.isdecimal() or not attempt.isdecimal():
        raise ValueError("invalid workflow identity")
    manifest = {"schema": "emdash-pages-artifact-v1", "sourceCommit": sha,
                "workflowRun": run, "workflowAttempt": attempt, "files": bundle_files(directory)}
    (directory / "validation.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def verify_manifest(directory: Path, sha: str, run: str, attempt: str) -> None:
    manifest = json.loads((directory / "validation.json").read_text())
    expected = {"schema": "emdash-pages-artifact-v1", "sourceCommit": sha,
                "workflowRun": run, "workflowAttempt": attempt}
    if any(manifest.get(key) != value for key, value in expected.items()):
        raise ValueError("artifact source/run identity differs from successful validation")
    for name in manifest.get("files", {}):
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or "\\" in name:
            raise ValueError("unsafe artifact path")
    if manifest.get("files") != bundle_files(directory):
        raise ValueError("artifact bytes or file membership changed after validation")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    base = sub.add_parser("base")
    base.add_argument("--runs", type=Path, required=True)
    base.add_argument("--repository", required=True)
    base.add_argument("--current", required=True)
    choose = sub.add_parser("select")
    choose.add_argument("--run", type=Path, required=True)
    choose.add_argument("--artifacts", type=Path, required=True)
    choose.add_argument("--repository", required=True)
    choose.add_argument("--manual", action="store_true")
    choose.add_argument("--current-main", action="store_true")
    for name in ("create", "verify"):
        command = sub.add_parser(name)
        command.add_argument("--directory", type=Path, required=True)
        command.add_argument("--sha", required=True)
        command.add_argument("--run", required=True)
        command.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if args.action == "base":
        value = qualified_base(json.loads(args.runs.read_text())["workflow_runs"], args.repository, args.current)
        print(value or "")
    elif args.action == "select":
        result = select_artifact(json.loads(args.run.read_text()), json.loads(args.artifacts.read_text())["artifacts"],
                                 args.repository, manual=args.manual)
        if result["deploy"] and args.current_main and not args.manual:
            repository_root = Path(__file__).resolve().parents[2]
            ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", result["sha"], "HEAD"], cwd=repository_root)
            if ancestor.returncode:
                result["deploy"] = False
            else:
                paths = subprocess.check_output(["git", "diff", "--no-renames", "--name-only", "-z", result["sha"], "HEAD", "--"],
                                                cwd=repository_root).decode().split("\0")
                spec = importlib.util.spec_from_file_location("emdash_devops", repository_root / "scripts/devops.py")
                devops = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(devops)
                if any(row["gate"] == "reviewer" for row in devops.select_gates([path for path in paths if path])["include"]):
                    result["deploy"] = False
        print(json.dumps(result))
        with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
            for name, value in result.items():
                stream.write(name + "=" + (str(value).lower() if isinstance(value, bool) else value) + "\n")
    elif args.action == "create":
        write_manifest(args.directory, args.sha, args.run, args.attempt)
    else:
        verify_manifest(args.directory, args.sha, args.run, args.attempt)
        print("Validated reviewer artifact identity and file digests match.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError) as error:
        raise SystemExit(str(error))
