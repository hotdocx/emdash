#!/usr/bin/env python3
"""Check an exact registered source copy using its measured target profile."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import os
from pathlib import Path
import sys

if __package__:
    from .check_registry import ROOT, input_hashes, load_registry, profile_for, source_dependencies
    from .run_lambdapi import outcome_exit_code, run_check
else:
    from check_registry import ROOT, input_hashes, load_registry, profile_for, source_dependencies
    from run_lambdapi import outcome_exit_code, run_check


@contextmanager
def target_environment(profile: dict):
    previous = dict(os.environ)
    try:
        os.environ.setdefault("EMDASH_LP_MEMORY_MIB", str(profile["memoryMiB"]))
        deadline = next((previous[key] for key in (
            "EMDASH_PROBE_TIMEOUT", "EMDASH_LP_TIMEOUT", "EMDASH_TYPECHECK_TIMEOUT"
        ) if previous.get(key)), str(profile["timeoutSeconds"]) + "s")
        os.environ.setdefault("EMDASH_LP_TIMEOUT", deadline)
        if profile.get("ocamlrunparam"):
            os.environ.setdefault("OCAMLRUNPARAM", profile["ocamlrunparam"])
        yield
    finally:
        os.environ.clear()
        os.environ.update(previous)


def check_registered_stage(target: Path, package_root: Path, *, compile_object: bool = False,
                           formal_root: Path = ROOT) -> int:
    data = load_registry(formal_root)
    if str(target) not in set(data["core"] + data["reviewers"]):
        raise ValueError("not an exact registered target")
    expected = input_hashes([target], formal_root)
    if input_hashes([target], package_root) != expected:
        raise ValueError("staged sources or package configuration differ from registered inputs")
    order: list[Path] = []
    seen: set[Path] = set()

    def visit(path: Path):
        if path in seen:
            return
        seen.add(path)
        for dependency in source_dependencies(path, package_root):
            visit(dependency)
        artifact = package_root / path.with_suffix(".lpo")
        if artifact.is_file() and artifact.stat().st_size == 0:
            raise ValueError("empty staged object cannot be reused")
        if path != target and not artifact.is_file():
            order.append(path)

    if compile_object:
        visit(target)
    order.append(target)
    for current in order:
        if str(current) not in set(data["core"] + data["reviewers"]):
            raise ValueError("unregistered staged dependency")
        name, profile = profile_for(current, data)
        print(f"registered stage profile: {current}: {name}", flush=True)
        with target_environment(profile):
            receipt = run_check(current, package_root, compile_object=compile_object,
                                extra_flags=["--no-colors"])
        print(f'{current}: {receipt["outcome"]}; {receipt["wallSeconds"]:.3f}s; '
              f'receipt {receipt["id"]}', flush=True)
        if (input_hashes([target], formal_root) != expected or
                input_hashes([target], package_root) != expected):
            print("registered or staged inputs changed during staged check", file=sys.stderr)
            return 74
        code = outcome_exit_code(receipt["outcome"], receipt["checkerExit"])
        if code:
            return code
        if compile_object:
            artifact = package_root / current.with_suffix(".lpo")
            if not artifact.is_file() or artifact.stat().st_size == 0:
                print("staged compilation produced no usable object", file=sys.stderr)
                return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path, default=Path.cwd())
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("target", type=Path)
    args = parser.parse_args()
    try:
        return check_registered_stage(args.target, args.package_root,
                                      compile_object=args.compile)
    except (OSError, ValueError) as error:
        parser.exit(2, f"staged check rejected: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
