#!/usr/bin/env python3
"""Capture, verify, or install the pinned formal verification environment."""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "toolchains/verification.json"


def installed_packages():
    output = subprocess.check_output(
        ["opam", "list", "--installed", "--required-by=lambdapi", "--recursive", "--columns=name,version", "--short"],
        text=True, timeout=30,
    )
    return dict(line.split() for line in output.splitlines() if line.strip())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("verify", "install", "capture", "ci-outputs"))
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    if args.action == "ci-outputs":
        with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
            stream.write("ocaml=" + manifest["ocaml"] + "\n")
            stream.write("repository=" + manifest["opamRepository"] + "\n")
        return 0
    if args.action == "capture":
        # The source commit is deliberately reviewed separately from dependency capture.
        manifest["opamPackages"] = installed_packages()
        MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
        print("Captured installed package versions; review the exact manifest diff.")
        return 0
    if args.action == "install":
        if os.environ.get("CI") != "true" and os.environ.get("EMDASH_INSTALL_VERIFICATION_TOOLCHAIN") != "1":
            parser.error("use a dedicated opam switch and set EMDASH_INSTALL_VERIFICATION_TOOLCHAIN=1 to install locally")
        pin = manifest["lambdapi"]
        compiler = subprocess.check_output(["ocamlc", "-version"], text=True, timeout=5).strip()
        if compiler != manifest["ocaml"]:
            parser.error("create the pinned OCaml switch before installing dependencies")
        subprocess.run(["opam", "repository", "set-url", "default", manifest["opamRepository"], "--yes"], check=True)
        subprocess.run(["opam", "pin", "add", "--yes", "--no-action", "lambdapi",
                        "git+" + pin["repository"] + "#" + pin["commit"]], check=True)
        packages = [name + "." + version for name, version in manifest["opamPackages"].items()]
        subprocess.run(["opam", "install", "--yes", "--jobs=2", *packages], check=True)
    actual = installed_packages()
    mismatches = {name: {"expected": version, "actual": actual.get(name)}
                  for name, version in manifest["opamPackages"].items() if actual.get(name) != version}
    for name in sorted(set(actual) - set(manifest["opamPackages"])):
        mismatches[name] = {"expected": None, "actual": actual[name]}
    version = subprocess.check_output(["lambdapi", "--version"], text=True, timeout=5).strip()
    compiler = subprocess.check_output(["ocamlc", "-version"], text=True, timeout=5).strip()
    pin_list = subprocess.check_output(["opam", "pin", "list"], text=True, timeout=10)
    pin_matches = manifest["lambdapi"]["commit"] in pin_list
    result = {"packageMismatches": mismatches, "lambdapi": version, "ocaml": compiler,
              "sourcePinMatches": pin_matches}
    print(json.dumps(result, indent=2))
    return int(bool(mismatches) or version != manifest["lambdapi"]["version"]
               or compiler != manifest["ocaml"] or not pin_matches)


if __name__ == "__main__":
    raise SystemExit(main())
