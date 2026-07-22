#!/usr/bin/env python3
"""Validate the book evidence register against active repository sources."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent
BOOK_MANIFEST = REPO_ROOT / "book" / "book.json"
EVIDENCE_PATH = REPO_ROOT / "book" / "evidence.json"
CLAIM_ID_RE = re.compile(r"^[A-Z][A-Z0-9-]*$")
EVIDENCE_MARKER_RE = re.compile(r"<!--\s*evidence:([A-Z][A-Z0-9-]*)\s*-->")
ALLOWED_STATUSES = {
    "checked",
    "formal-consequence",
    "mathematical-development",
    "research-boundary",
}
ACTIVE_OWNER_FILES = {
    "emdash3_2.lp",
    "emdash3_2_eq1_hom_action.lp",
    "emdash3_2_eq1_evidence_property.lp",
    "emdash3_2_nat_arithmetic.lp",
    "emdash3_2_walking_end_hit.lp",
}


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise ValueError(f"{path.relative_to(REPO_ROOT)} is missing") from None
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"{path.relative_to(REPO_ROOT)}:{exc.lineno}:{exc.colno}: {exc.msg}"
        ) from None


def resolve_repo_file(raw: Any, context: str) -> Path:
    if not isinstance(raw, str) or not raw:
        raise ValueError(f"{context}: file must be a non-empty repository-relative path")
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError(f"{context}: unsafe repository path {raw!r}")
    resolved = (REPO_ROOT / relative).resolve()
    try:
        resolved.relative_to(REPO_ROOT)
    except ValueError:
        raise ValueError(f"{context}: path escapes the repository: {raw!r}") from None
    if not resolved.is_file():
        raise ValueError(f"{context}: file does not exist: {raw}")
    return resolved


def reference_role_issue(relative: str, *, owner: bool) -> str | None:
    if owner:
        if relative not in ACTIVE_OWNER_FILES:
            return f"owner must be an active Lambdapi module, got {relative}"
        return None
    if relative == "emdash3_2_checks.lp":
        return None
    if relative.startswith("examples/") and relative.endswith(".lp"):
        return None
    return (
        "reviewer must be emdash3_2_checks.lp or a reviewer example, "
        f"got {relative}"
    )


def validate_reference(ref: Any, context: str, *, owner: bool) -> str:
    if not isinstance(ref, dict):
        raise ValueError(f"{context}: reference must be an object")
    unknown = set(ref) - {"file", "symbol", "contains"}
    if unknown:
        raise ValueError(f"{context}: unknown reference fields: {sorted(unknown)}")

    path = resolve_repo_file(ref.get("file"), context)
    relative = path.relative_to(REPO_ROOT).as_posix()
    role_issue = reference_role_issue(relative, owner=owner)
    if role_issue is not None:
        raise ValueError(f"{context}: {role_issue}")
    text = path.read_text(encoding="utf-8")
    symbol = ref.get("symbol")
    contains = ref.get("contains")
    if bool(symbol) == bool(contains):
        raise ValueError(f"{context}: provide exactly one of symbol or contains")

    if symbol:
        if not isinstance(symbol, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", symbol):
            raise ValueError(f"{context}: invalid symbol name {symbol!r}")
        if owner:
            declaration = re.compile(
                rf"^\s*(?:(?:constant|injective|sequential|opaque|private|protected)\s+)*"
                rf"symbol\s+{re.escape(symbol)}\b",
                re.MULTILINE,
            )
            if declaration.search(text) is None:
                raise ValueError(
                    f"{context}: owner declaration {symbol!r} not found in "
                    f"{path.relative_to(REPO_ROOT)}"
                )
        elif re.search(rf"\b{re.escape(symbol)}\b", text) is None:
            raise ValueError(
                f"{context}: reviewer token {symbol!r} not found in "
                f"{path.relative_to(REPO_ROOT)}"
            )
    elif not isinstance(contains, str) or not contains:
        raise ValueError(f"{context}: contains must be a non-empty string")
    elif contains not in text:
        raise ValueError(
            f"{context}: reviewer text {contains!r} not found in "
            f"{path.relative_to(REPO_ROOT)}"
        )
    return relative


def manifest_source_markers(manifest: Any) -> set[str]:
    if not isinstance(manifest, dict) or manifest.get("version") != 1:
        raise ValueError("book/book.json: expected manifest version 1")
    sources = manifest.get("sources")
    if not isinstance(sources, list) or not sources:
        raise ValueError("book/book.json: sources must be a non-empty list")

    markers: set[str] = set()
    seen_source_ids: set[str] = set()
    for index, source in enumerate(sources):
        context = f"book/book.json:sources[{index}]"
        if not isinstance(source, dict):
            raise ValueError(f"{context}: source must be an object")
        source_id = source.get("id")
        if not isinstance(source_id, str) or not source_id:
            raise ValueError(f"{context}: id must be non-empty")
        if source_id in seen_source_ids:
            raise ValueError(f"{context}: duplicate source id {source_id!r}")
        seen_source_ids.add(source_id)
        path = resolve_repo_file(source.get("path"), context)
        markers.update(EVIDENCE_MARKER_RE.findall(path.read_text(encoding="utf-8")))
    return markers


def main() -> int:
    issues: list[str] = []
    try:
        manifest = load_json(BOOK_MANIFEST)
        evidence = load_json(EVIDENCE_PATH)
        markers = manifest_source_markers(manifest)

        if not isinstance(evidence, dict) or evidence.get("version") != 1:
            raise ValueError("book/evidence.json: expected evidence version 1")
        declared_statuses = evidence.get("statuses")
        if set(declared_statuses or []) != ALLOWED_STATUSES:
            raise ValueError(
                "book/evidence.json: statuses must declare exactly "
                + ", ".join(sorted(ALLOWED_STATUSES))
            )
        claims = evidence.get("claims")
        if not isinstance(claims, dict) or not claims:
            raise ValueError("book/evidence.json: claims must be a non-empty object")

        for claim_id, claim in claims.items():
            context = f"book/evidence.json:claims.{claim_id}"
            if not CLAIM_ID_RE.fullmatch(claim_id):
                issues.append(f"{context}: invalid claim id")
                continue
            if not isinstance(claim, dict):
                issues.append(f"{context}: claim must be an object")
                continue
            status = claim.get("status")
            if status not in ALLOWED_STATUSES:
                issues.append(f"{context}: invalid status {status!r}")
            statement = claim.get("statement")
            if not isinstance(statement, str) or not statement.strip():
                issues.append(f"{context}: statement must be non-empty")

            owners = claim.get("owners", [])
            reviewers = claim.get("reviewers", [])
            if status in {"checked", "formal-consequence"} and not owners:
                issues.append(f"{context}: {status} claim requires at least one owner")
            if status == "checked" and not reviewers:
                issues.append(f"{context}: checked claim requires reviewer/check evidence")

            if not isinstance(owners, list):
                issues.append(f"{context}: owners must be a list")
            else:
                owner_files: set[str] = set()
                for index, ref in enumerate(owners):
                    try:
                        owner_files.add(
                            validate_reference(
                                ref, f"{context}.owners[{index}]", owner=True
                            )
                        )
                    except ValueError as exc:
                        issues.append(str(exc))

            if not isinstance(reviewers, list):
                issues.append(f"{context}: reviewers must be a list")
            else:
                reviewer_files: set[str] = set()
                for index, ref in enumerate(reviewers):
                    try:
                        reviewer_files.add(
                            validate_reference(
                                ref, f"{context}.reviewers[{index}]", owner=False
                            )
                        )
                    except ValueError as exc:
                        issues.append(str(exc))

            if (
                status == "checked"
                and isinstance(owners, list)
                and isinstance(reviewers, list)
                and owner_files & reviewer_files
            ):
                issues.append(
                    f"{context}: checked claim reviewer must be independent of "
                    f"owner file(s): {sorted(owner_files & reviewer_files)}"
                )

        unknown_markers = markers - set(claims)
        unused_checked = {
            claim_id
            for claim_id, claim in claims.items()
            if isinstance(claim, dict)
            and claim.get("status") == "checked"
            and claim_id not in markers
        }
        for claim_id in sorted(unknown_markers):
            issues.append(f"book source uses unknown evidence marker {claim_id}")
        for claim_id in sorted(unused_checked):
            issues.append(f"checked evidence claim is not cited by a manifest source: {claim_id}")
    except ValueError as exc:
        issues.append(str(exc))

    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1

    print(
        f"book evidence check passed: {len(claims)} claim(s), "
        f"{len(markers)} cited evidence id(s)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
