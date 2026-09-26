#!/usr/bin/env python3
"""Run one source check through the repository guard and save exact evidence."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
import platform
from pathlib import Path
import re
import resource
import shlex
import shutil
import subprocess
import sys
import time
import uuid

if __package__:
    from .check_registry import ROOT, digest_inputs, input_hashes, local_file, profile_for
else:
    from check_registry import ROOT, digest_inputs, input_hashes, local_file, profile_for


def file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def duration_ms(value: str) -> int:
    if not re.fullmatch(r"[1-9][0-9]{0,2}s?", value):
        raise ValueError("timeout must be 1..600 whole seconds")
    result = int(value.removesuffix("s")) * 1000
    if result > 600_000:
        raise ValueError("timeout exceeds 600 seconds")
    return result


def execution_settings(target: Path, env: dict[str, str], timeout_ms: int | None = None) -> dict:
    profile_name, profile = profile_for(target)
    if timeout_ms is None:
        override = next((env[key] for key in ("EMDASH_PROBE_TIMEOUT", "EMDASH_LP_TIMEOUT", "EMDASH_TYPECHECK_TIMEOUT") if env.get(key)), None)
        timeout_ms = duration_ms(override) if override else profile["timeoutSeconds"] * 1000
    if not 1 <= timeout_ms <= 600_000:
        raise ValueError("timeout must be 1..600000 milliseconds")
    memory = int(env.get("EMDASH_LP_MEMORY_MIB", str(profile["memoryMiB"])))
    file_limit = int(env.get("EMDASH_LP_FILE_MIB", "64"))
    if not 32 <= memory <= 6144 or not 1 <= file_limit <= 64:
        raise ValueError("resource limits exceed the reviewed bounds")
    warnings = env.get("EMDASH_LAMBDAPI_WARNINGS", "0").lower()
    if warnings not in {"1", "true", "yes", "on", "0", "false", "no", "off"}:
        raise ValueError("invalid EMDASH_LAMBDAPI_WARNINGS")
    flags = shlex.split(env.get("EMDASH_LAMBDAPI_FLAGS", ""))
    if any(flag.split("=", 1)[0] == "--no-sr-check" for flag in flags):
        raise ValueError("subject reduction cannot be disabled")
    return {
        "profile": profile_name, "timeoutMs": timeout_ms, "memoryMiB": memory,
        "fileMiB": file_limit, "resourceBackend": env.get("EMDASH_LP_RESOURCE_BACKEND", "auto"),
        "ocamlrunparam": env.get("OCAMLRUNPARAM", profile.get("ocamlrunparam", "")),
        "camlrunparam": env.get("CAMLRUNPARAM", ""),
        "runtimeEnvironment": {key: env.get(key, "") for key in ("CAML_LD_LIBRARY_PATH", "LD_LIBRARY_PATH", "LD_PRELOAD")},
        "pythonVersion": sys.version,
        "platform": platform.platform(),
        "flags": ([] if warnings in {"1", "true", "yes", "on"} else ["-w"]) + flags,
    }


def checker_identity(binary: Path) -> dict:
    version = subprocess.run([str(binary), "--version"], capture_output=True, text=True, timeout=5)
    if version.returncode:
        raise ValueError("could not identify Lambdapi version")
    return {"path": str(binary), "sha256": file_digest(binary), "version": version.stdout.strip()}


def tooling_inputs() -> dict[str, str]:
    paths = [ROOT / "checks.json", *sorted((ROOT / "scripts").glob("*.py")),
             *sorted((ROOT / "scripts").glob("*.sh"))]
    return {str(path.relative_to(ROOT)): file_digest(path) for path in paths}


def retain_inputs(inputs: dict[str, str], package_root: Path) -> str:
    store = ROOT / "logs/check-inputs"
    store.mkdir(parents=True, exist_ok=True)
    for name, digest in inputs.items():
        content = local_file(package_root, name).read_bytes()
        if hashlib.sha256(content).hexdigest() != digest:
            raise ValueError(f"input changed while capturing evidence: {name}")
        destination = store / digest
        try:
            with destination.open("xb") as stream:
                stream.write(content)
        except FileExistsError:
            if file_digest(destination) != digest:
                raise ValueError(f"retained input digest mismatch: {digest}")
    return str(store.relative_to(ROOT))


def classify_exit(code: int, elapsed: float, settings: dict, output: str) -> str:
    # Lambdapi can return zero after an uncaught object-serialization failure.
    # Preserve the process status, but never qualify that diagnostic as success.
    plain_output = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", output)
    fatal = re.search(r"^(?:Uncaught \[|Fatal error:)", plain_output, re.MULTILINE)
    if code == 0 and not fatal:
        return "passed-fresh"
    if code == 75:
        return "busy"
    if code in (-9, 137, 124) and elapsed >= settings["timeoutMs"] / 1000:
        return "timeout"
    if any(message in plain_output.lower() for message in
           ("out of memory", "cannot allocate memory", "allocation failure")):
        return "allocation-failed"
    if code in (-9, 137):
        return "killed-unknown-cause"
    return "failed"


def outcome_exit_code(outcome: str, process_code: int) -> int:
    if outcome == "timeout":
        return 124
    if outcome == "inputs-changed":
        return 74
    if process_code == 0 and outcome != "passed-fresh":
        return 1
    return process_code if process_code >= 0 else 128 - process_code


def run_check(target: Path, package_root: Path, *, timeout_ms: int | None = None,
              compile_object: bool = False, extra_flags: list[str] | None = None) -> dict:
    package_root = package_root.resolve()
    if target.is_absolute():
        target = target.resolve().relative_to(package_root)
    local_file(package_root, str(target))
    local_file(package_root, "lambdapi.pkg")
    env = dict(os.environ)
    # Scratch copies and external probe packages do not inherit privileged
    # target profiles just because their relative filename matches an owner.
    profile_target = target if package_root == ROOT else Path("tmp") / target
    settings = execution_settings(profile_target, env, timeout_ms)
    flags = [*settings["flags"], *(extra_flags or [])]
    if any(flag.split("=", 1)[0] == "--no-sr-check" for flag in flags):
        raise ValueError("subject reduction cannot be disabled")
    settings["flags"] = flags
    binary_name = shutil.which("lambdapi")
    if binary_name is None:
        raise ValueError("lambdapi is unavailable")
    binary = Path(binary_name).resolve()
    checker = checker_identity(binary)
    before = input_hashes([target], package_root, objects=True)
    input_store = retain_inputs(before, package_root)
    runners = tooling_inputs()
    retain_inputs(runners, ROOT)
    env.update({
        "EMDASH_LP_MEMORY_MIB": str(settings["memoryMiB"]),
        "EMDASH_LP_FILE_MIB": str(settings["fileMiB"]),
        "EMDASH_LP_TIMEOUT": str(math.ceil(settings["timeoutMs"] / 1000)) + "s",
        "EMDASH_LP_RESOURCE_BACKEND": settings["resourceBackend"],
    })
    if settings["ocamlrunparam"]:
        env["OCAMLRUNPARAM"] = settings["ocamlrunparam"]
    arguments = [str(binary), "check", *( ["-c"] if compile_object else []), *flags, str(target)]
    # The outer guard remains whole-second bounded; preserve the existing TS
    # API's finer deadline with an inner hard timeout when necessary.
    if settings["timeoutMs"] % 1000:
        arguments = ["timeout", "--signal=KILL", f'{settings["timeoutMs"] / 1000:g}s', *arguments]
    command = ["bash", str(ROOT / "scripts/lambdapi_resource_guard.sh"), *arguments]
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex
    directory = ROOT / "logs/check-runs"
    directory.mkdir(parents=True, exist_ok=True)
    log = directory / (run_id + ".log")
    started = time.monotonic()
    with log.open("x") as stream:
        process = subprocess.run(command, cwd=package_root, env=env, stdout=stream, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    output = log.read_text(errors="replace")
    outcome = classify_exit(process.returncode, elapsed, settings, output)
    try:
        after = input_hashes([target], package_root, objects=True)
    except (OSError, ValueError):
        after = {}
    # -c intentionally creates objects; source changes always invalidate.
    comparable_after = {name: after.get(name) for name in before}
    stable = before == comparable_after and file_digest(binary) == checker["sha256"] and runners == tooling_inputs()
    if not stable and outcome == "passed-fresh":
        outcome = "inputs-changed"
    actual_backend = re.search(r"resource guard: backend=(\w+)", output)
    receipt = {
        "schema": "emdash-check-receipt-v1", "id": run_id, "target": str(target),
        "kind": "source-check", "packageRoot": str(package_root), "command": command,
        "checker": checker, "inputs": before, "inputSnapshot": digest_inputs(before),
        "inputStore": input_store,
        "runnerInputs": runners, "settings": settings, "compileObject": compile_object,
        "observedResourceBackend": actual_backend.group(1) if actual_backend else None,
        "outcome": outcome, "checkerExit": process.returncode, "wallSeconds": elapsed,
        "childrenMaxRssKiB": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss if sys.platform == "linux" else None,
        "memoryMeasurement": "maximum child-process RSS; not aggregate descendant memory",
        "reusable": outcome == "passed-fresh" and stable,
        "log": str(log.relative_to(ROOT)), "logSha256": file_digest(log),
        "theoryQualification": "execution evidence only; current source/profile qualifications remain",
    }
    receipt_path = directory / (run_id + ".json")
    with receipt_path.open("x") as stream:
        json.dump(receipt, stream, indent=2, sort_keys=True)
        stream.write("\n")
    return {**receipt, "receiptPath": str(receipt_path)}


def run_staged_group(script: str, targets: list[Path], env: dict[str, str]) -> tuple[int, str, float]:
    """Record the owned recipe as a group; each checker inside keeps its guard."""
    local_file(ROOT, script.removeprefix("./"))
    settings = execution_settings(Path("staged-recipe"), env)
    binary_name = shutil.which("lambdapi")
    if binary_name is None:
        raise ValueError("lambdapi is unavailable")
    binary = Path(binary_name).resolve()
    checker = checker_identity(binary)
    before = input_hashes(targets, ROOT, objects=True)
    input_store = retain_inputs(before, ROOT)
    runners = tooling_inputs()
    retain_inputs(runners, ROOT)
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex
    directory = ROOT / "logs/check-runs"
    directory.mkdir(parents=True, exist_ok=True)
    log = directory / (run_id + ".log")
    started = time.monotonic()
    with log.open("x") as stream:
        result = subprocess.run([script], cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    try:
        stable = before == input_hashes(targets, ROOT, objects=True)
    except (OSError, ValueError):
        stable = False
    stable = stable and runners == tooling_inputs() and checker["sha256"] == file_digest(binary)
    output = log.read_text(errors="replace")
    # A recipe's total duration is not a per-child deadline. Retain its
    # failure scope while rejecting fatal child output even after exit zero.
    outcome = classify_exit(0, elapsed, settings, output) if result.returncode == 0 else "failed"
    if not stable and outcome == "passed-fresh":
        outcome = "inputs-changed"
    receipt = {
        "schema": "emdash-check-receipt-v1", "id": run_id, "kind": "staged-check",
        "targets": list(map(str, targets)), "packageRoot": str(ROOT), "command": [script],
        "inputs": before, "inputSnapshot": digest_inputs(before), "inputStore": input_store,
        "runnerInputs": runners, "checker": checker, "settings": settings,
        "profilePolicy": "per-child guards and explicit runtime overrides owned by the recorded recipe",
        "wallSeconds": elapsed, "timingScope": "whole group including prerequisites; not individual target timings",
        "outcome": outcome, "recipeExit": result.returncode, "reusable": outcome == "passed-fresh",
        "log": str(log.relative_to(ROOT)), "logSha256": file_digest(log),
        "theoryQualification": "execution evidence only; current source/profile qualifications remain",
    }
    receipt_path = directory / (run_id + ".json")
    with receipt_path.open("x") as stream:
        json.dump(receipt, stream, indent=2, sort_keys=True)
        stream.write("\n")
    code = outcome_exit_code(outcome, result.returncode)
    return code, output + f"\nreceipt: {receipt_path}\n", elapsed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", type=Path)
    parser.add_argument("--package-root", type=Path, default=ROOT)
    parser.add_argument("--timeout-ms", type=int)
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("--no-colors", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()
    try:
        receipt = run_check(args.target, args.package_root, timeout_ms=args.timeout_ms,
                            compile_object=args.compile, extra_flags=["--no-colors"] if args.no_colors else [])
        if args.json:
            print(json.dumps(receipt))
        elif args.quiet:
            print(f'{receipt["target"]}: {receipt["outcome"]}; {receipt["wallSeconds"]:.3f}s')
            print(f'log: {ROOT / receipt["log"]}')
            print(f'receipt: {receipt["receiptPath"]}')
            if receipt["outcome"] != "passed-fresh":
                print("\n".join((ROOT / receipt["log"]).read_text(errors="replace").splitlines()[-40:]), file=sys.stderr)
        else:
            print((ROOT / receipt["log"]).read_text(errors="replace"), end="")
            print(f'receipt: {receipt["receiptPath"]}', file=sys.stderr)
        return outcome_exit_code(receipt["outcome"], receipt["checkerExit"])
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"checker setup failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
