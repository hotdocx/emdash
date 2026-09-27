"""Operational targets and exact local Lambdapi dependency identity.

This is a build inventory, not a parser or mathematical authority. Unsupported
import syntax and unresolved/external imports fail closed for evidence reuse.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = ROOT / "checks.json"


def local_file(root: Path, name: str) -> Path:
    path = Path(name)
    if path.is_absolute() or ".." in path.parts or not name:
        raise ValueError(f"not a local relative input: {name}")
    resolved = (root / path).resolve()
    if not resolved.is_relative_to(root.resolve()) or not resolved.is_file():
        raise ValueError(f"missing or escaping input: {name}")
    return resolved


def load_registry(root: Path = ROOT) -> dict:
    data = json.loads((root / "checks.json").read_text())
    if data.get("version") != 1:
        raise ValueError("unsupported check registry version")
    for key in ("core", "reviewers", "check", "priority"):
        values = data.get(key)
        if not isinstance(values, list) or not all(isinstance(v, str) for v in values):
            raise ValueError(f"invalid target list: {key}")
        if len(values) != len(set(values)):
            raise ValueError(f"duplicate targets in {key}")
        for value in values:
            if Path(value).suffix != ".lp":
                raise ValueError(f"not an LP target: {value}")
            local_file(root, value)
    all_targets = set(data["core"]) | set(data["reviewers"])
    if set(data["core"]) & set(data["reviewers"]):
        raise ValueError("core and reviewer classifications overlap")
    for key in ("check", "priority"):
        if not set(data[key]) <= all_targets:
            raise ValueError(f"unknown targets in {key}")
    grouped: set[str] = set()
    ids: set[str] = set()
    for group in data["isolatedGroups"]:
        targets = group["targets"]
        if group["id"] in ids or not targets or len(targets) != len(set(targets)):
            raise ValueError("duplicate or empty isolated group")
        if not set(targets) <= all_targets or grouped & set(targets):
            raise ValueError("unknown or overlapping isolated targets")
        local_file(root, group["script"])
        ids.add(group["id"])
        grouped.update(targets)
    profiled: set[str] = set()
    for name, targets in data["profileTargets"].items():
        if name not in data["profiles"] or not set(targets) <= all_targets:
            raise ValueError("unknown profile or profile targets")
        if len(targets) != len(set(targets)) or profiled & set(targets):
            raise ValueError("duplicate or overlapping profile targets")
        profiled.update(targets)
    overrides = data.get("targetProfileOverrides", {})
    if not isinstance(overrides, dict) or any(
        target not in all_targets or not isinstance(profile, str) or profile not in data["profiles"]
        for target, profile in overrides.items()
    ):
        raise ValueError("unknown target or profile in target profile overrides")
    for name, profile in data["profiles"].items():
        if (type(profile["memoryMiB"]) is not int or type(profile["timeoutSeconds"]) is not int
                or not 32 <= profile["memoryMiB"] <= 8192 or not 1 <= profile["timeoutSeconds"] <= 600):
            raise ValueError(f"out-of-bounds profile: {name}")
    if "default" not in data["profiles"]:
        raise ValueError("missing default profile")
    return data


def inventory_issues(data: dict, root: Path = ROOT) -> list[str]:
    issues = []
    for key, pattern in (("core", "*.lp"), ("reviewers", "examples/*.lp")):
        actual = {p.relative_to(root).as_posix() for p in root.glob(pattern)}
        registered = set(data[key])
        for name in sorted(actual - registered):
            issues.append(f"unregistered {key} source: {name}")
        for name in sorted(registered - actual):
            issues.append(f"missing {key} source: {name}")
    return issues


def mask_comments_and_strings(source: str) -> str:
    """Hide nested block comments, line comments and strings before import scan."""
    pieces = []
    start = 0
    marker = re.compile(r'/\*|//|"')
    block_marker = re.compile(r'/\*|\*/')
    while (token := marker.search(source, start)) is not None:
        pieces.append(source[start:token.start()])
        pieces.append(" ")
        value = token.group()
        start = token.end()
        if value == "/*":
            depth = 1
            while depth:
                end = block_marker.search(source, start)
                if end is None:
                    raise ValueError("unterminated source comment")
                depth += 1 if end.group() == "/*" else -1
                start = end.end()
        elif value == "//":
            end = source.find("\n", start)
            start = len(source) if end == -1 else end
        else:
            end = re.compile(r'(?:\\.|[^"\\])*"').match(source, start)
            if end is None:
                raise ValueError("unterminated source string")
            start = end.end()
    pieces.append(source[start:])
    return "".join(pieces)


def source_dependencies(path: Path, root: Path = ROOT) -> list[Path]:
    source = mask_comments_and_strings(local_file(root, str(path)).read_text())
    statements = list(re.finditer(r"\brequire\s+([^;]+);", source))
    if len(statements) != len(re.findall(r"\brequire\b", source)):
        raise ValueError(f"unresolved require syntax in {path}")
    if not statements:
        return []
    config = local_file(root, "lambdapi.pkg").read_text()
    prefix = re.search(r"^\s*root_path\s*=\s*([A-Za-z0-9_.]+)\s*$", config, re.M)
    if prefix is None:
        raise ValueError("unsupported lambdapi.pkg root_path")
    namespace = prefix.group(1) + "."
    result = []
    for statement in statements:
        names = statement.group(1).split()
        if names and names[0] == "open":
            names.pop(0)
        if not names:
            raise ValueError(f"empty require in {path}")
        for name in names:
            if not re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", name) or not name.startswith(namespace):
                raise ValueError(f"unsupported/external import {name!r} in {path}")
            relative = Path(*name[len(namespace):].split(".")).with_suffix(".lp")
            local_file(root, str(relative))
            result.append(relative)
    return result


def source_closure(files: list[Path], root: Path = ROOT) -> list[Path]:
    visited: set[Path] = set()
    pending = list(files)
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        local_file(root, str(path))
        visited.add(path)
        pending.extend(source_dependencies(path, root))
    return sorted(visited, key=str)


def input_hashes(files: list[Path], root: Path = ROOT, *, objects: bool = False) -> dict[str, str]:
    paths = source_closure(files, root)
    config = root / "lambdapi.pkg"
    if config.exists():
        paths.append(Path("lambdapi.pkg"))
    if objects:
        for source in list(paths):
            if source.suffix == ".lp":
                for extension in (".lpo", ".lpi", ".lpj"):
                    artifact = source.with_suffix(extension)
                    if (root / artifact).exists():
                        paths.append(artifact)
    return {str(path): hashlib.sha256(local_file(root, str(path)).read_bytes()).hexdigest()
            for path in sorted(paths, key=str)}


def digest_inputs(inputs: dict) -> str:
    return hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def profile_for(target: Path, data: dict | None = None) -> tuple[str, dict]:
    data = data if data is not None else load_registry()
    name = next((name for name, paths in data["profileTargets"].items() if str(target) in paths), "default")
    name = data.get("targetProfileOverrides", {}).get(str(target), name)
    return name, dict(data["profiles"][name])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", choices=("core", "reviewers", "check", "all"))
    args = parser.parse_args()
    try:
        data = load_registry()
        issues = inventory_issues(data)
        if issues:
            raise ValueError("\n".join(issues))
        files = [Path(x) for x in data["core"] + data["reviewers"]]
        closure = source_closure(files)
        if args.list:
            print("\n".join(map(str, files)) if args.list == "all" else "\n".join(data[args.list]))
        else:
            print(f"check registry passed: {len(files)} targets, {len(closure)} source dependencies")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(2, f"check registry failed: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
