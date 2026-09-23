#!/usr/bin/env python3
"""Keep historical profile entry points backed by the shared registry."""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess

if __package__:
    from .check_registry import ROOT, load_registry
else:
    from check_registry import ROOT, load_registry


def main() -> int:
    data = load_registry()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=tuple(data["profileTargets"]))
    parser.add_argument("target", nargs="?")
    args = parser.parse_args()
    files = data["profileTargets"][args.profile]
    if not files or (args.target is not None and args.target not in files):
        parser.error("not a registered target of this profile")
    profile = data["profiles"][args.profile]
    env = dict(os.environ)
    env.setdefault("EMDASH_LP_MEMORY_MIB", str(profile["memoryMiB"]))
    env.setdefault("OCAMLRUNPARAM", profile.get("ocamlrunparam", ""))
    default_timeout = str(profile["timeoutSeconds"]) + "s"
    if args.profile != "native-snake-pair":
        default_timeout = env.get("EMDASH_TYPECHECK_TIMEOUT", default_timeout)
    env.setdefault("EMDASH_PROBE_TIMEOUT", default_timeout)
    for target in [args.target] if args.target else files:
        result = subprocess.run([str(ROOT / "scripts/probe.sh"), target], cwd=ROOT, env=env)
        if result.returncode:
            return result.returncode if result.returncode >= 0 else 128 - result.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
