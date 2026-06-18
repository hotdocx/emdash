#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKS = ROOT / "emdash3_2_checks.lp"
REPORT = ROOT / "reports" / "REPORT_EMDASH_CHECK_CATALOG.md"


@dataclass(frozen=True)
class Check:
    index: int
    line: int
    source_line: int | None
    first_line: str
    statement: str


@dataclass(frozen=True)
class Area:
    title: str
    patterns: tuple[str, ...]


def read_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8").splitlines()


def parse_checks(lines: list[str]) -> list[Check]:
    checks: list[Check] = []
    source_line: int | None = None
    from_pattern = re.compile(r"^//\s+From emdash3_2\.lp:([0-9]+)\.")
    i = 0
    while i < len(lines):
        line = lines[i]
        line_no = i + 1
        from_match = from_pattern.match(line)
        if from_match:
            source_line = int(from_match.group(1))
            i += 1
            continue
        if line.lstrip().startswith("assert"):
            block = [line.strip()]
            j = i
            if not line.strip().endswith(";"):
                j = i + 1
                while j < len(lines):
                    block.append(lines[j].strip())
                    if lines[j].strip().endswith(";"):
                        break
                    j += 1
            checks.append(
                Check(
                    index=len(checks) + 1,
                    line=line_no,
                    source_line=source_line,
                    first_line=line.strip(),
                    statement=" ".join(block),
                )
            )
            source_line = None
            i = j + 1
            continue
        i += 1
    return checks


AREAS: list[Area] = [
    Area(
        "Path/equality category calculus",
        ("Path_cat", "eq_refl", "eq_trans"),
    ),
    Area(
        "Applications: PathOut, path induction, transitivity, telescopes",
        ("PathOut", "PathInd", "path_comp", "CompTarget", "Nested_", "Telescope"),
    ),
    Area(
        "Adjunction triangle cut-elimination",
        ("Adjunction", "left_adj", "right_adj", "unit_adj", "counit_adj"),
    ),
    Area(
        "Cat-valued profunctor facade",
        ("Prof_base", "Prof_cat", "Prof_reindex", "Hom_prof", "Unit_prof"),
    ),
    Area(
        "Products, evaluation, curry/uncurry",
        ("Product", "Eval", "curry", "uncurry"),
    ),
    Area(
        "Sigma/Pi totals, sections, and directed family calculus",
        (
            "Sigma",
            "sigma_",
            "Pi_",
            "Pi_cat",
            "piapp",
            "Const_catd",
            "Pullback_catd",
            "Catd_cat_func",
        ),
    ),
    Area(
        "Dependent homs and covariant fibre transport",
        (
            "homd",
            "Homd",
            "fib_cov",
            "FibCov",
            "HomPresheaf",
            "Rep_catd",
            "Edge_catd",
        ),
    ),
    Area(
        "Displayed hom-action and laxity extraction",
        ("tdapp", "fdapp", "Fibre_transf", "catd_transport", "functord_transport"),
    ),
    Area(
        "Universe categories and displayed-family category heads",
        (
            "Obj Grpd_cat",
            "Obj Cat_cat",
            "Hom_cat Cat_cat",
            "Functor_cat K Cat_cat",
            "Hom_cat (Catd_cat K)",
            "Hom_cat (Functord_cat E D) FF GG ≡ Transfd_cat",
            "Hom_cat (Functor_cat K Cat_cat)",
            "≡ @id_transfd",
        ),
    ),
    Area(
        "Ordinary transformations and structural logic",
        (
            "Transf",
            "tapp",
            "Const_transf",
            "sym_func",
            "diag_func",
            "comp_cat_cov",
            "comp_cat_con",
        ),
    ),
    Area(
        "Ordinary internal hom and composition actions",
        ("hom_", "hom_con", "hom_int", "hom_postcomp", "hom_precomp", "comp_func"),
    ),
    Area(
        "Displayed families, fibres, and displayed functor structure",
        (
            "Fibre_cat",
            "Fibre_func",
            "Terminal_catd",
            "Op_catd",
            "Catd_catd_con",
            "Obj_func",
            "id_funcd",
            "Op_funcd",
            "comp_catd_fapp0",
            "Functor_catd",
        ),
    ),
    Area(
        "Ordinary functor identity/composition laws",
        (
            "comp_cat_fapp0",
            "fapp1_fapp0",
            "fapp1_func",
            "id_func",
            "fapp0_func",
            "Const_func",
        ),
    ),
]


def classify(check: Check) -> str:
    text = check.statement
    for area in AREAS:
        if any(pattern in text for pattern in area.patterns):
            return area.title
    return "Other / unclassified checks"


def summarize(checks: list[Check]) -> dict[str, list[Check]]:
    grouped: dict[str, list[Check]] = {area.title: [] for area in AREAS}
    for check in checks:
        grouped.setdefault(classify(check), []).append(check)
    return {area: items for area, items in grouped.items() if items}


def short(text: str, limit: int = 120) -> str:
    clean = " ".join(text.split())
    if len(clean) <= limit:
        return clean
    return clean[: limit - 4].rstrip() + " ..."


def render() -> str:
    checks = parse_checks(read_lines(CHECKS))
    grouped = summarize(checks)
    unclassified = grouped.get("Other / unclassified checks", [])
    legacy_source_tags = sum(1 for check in checks if check.source_line is not None)

    lines: list[str] = [
        "# EMDASH Check Catalog",
        "",
        "This report is generated by `scripts/generate_check_catalog.py` from",
        "`emdash3_2_checks.lp`.",
        "",
        "It is intended as a reviewer-facing map of the regression suite, not as",
        "the source of truth for the checked statements.",
        "",
        "`emdash3_2_checks.lp` still contains legacy",
        "`// From emdash3_2.lp:<line>` comments from an older pre-split",
        "snapshot. This report deliberately does not present those as active",
        "source locations; the grouping below is based on the checked statement",
        "text.",
        "",
        "## Summary",
        "",
        f"- Total checks: {len(checks)}",
        f"- Mapped areas: {len(grouped)}",
        f"- Legacy source-line tags: {legacy_source_tags}",
        f"- Unclassified checks: {len(unclassified)}",
        "",
        "| Area | Checks |",
        "| --- | ---: |",
    ]

    for area, items in grouped.items():
        lines.append(f"| {area} | {len(items)} |")

    lines.extend([
        "",
        "## Section Details",
        "",
    ])

    for area, items in grouped.items():
        lines.extend([
            f"### {area}",
            "",
            "| # | Check line | Statement |",
            "| ---: | ---: | --- |",
        ])
        for check in items:
            lines.append(
                f"| {check.index} | {check.line} | `{short(check.statement)}` |"
            )
        lines.append("")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate the reviewer-facing EMDASH check catalog."
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit 1 if the generated report differs from the checked-in file.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit 1 if any assertion is not classified into a reviewer-facing area.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=REPORT,
        help="Output path for the generated markdown report.",
    )
    args = parser.parse_args()

    def display(path: Path) -> str:
        try:
            return str(path.relative_to(ROOT))
        except ValueError:
            return str(path)

    checks = parse_checks(read_lines(CHECKS))
    grouped = summarize(checks)
    content = render()
    unclassified = grouped.get("Other / unclassified checks", [])
    if unclassified and args.strict:
        print(
            "Some checks are unclassified; update AREAS in "
            "scripts/generate_check_catalog.py.",
            file=sys.stderr,
        )
        for check in unclassified[:10]:
            print(
                f"- check #{check.index} at line {check.line}: {short(check.statement, 100)}",
                file=sys.stderr,
            )
        return 1
    if unclassified:
        print(
            f"warning: {len(unclassified)} check(s) are unclassified; "
            "CI uses --strict and will fail until AREAS is updated.",
            file=sys.stderr,
        )
    output = args.output if args.output.is_absolute() else ROOT / args.output
    if args.check:
        existing = output.read_text(encoding="utf-8") if output.exists() else ""
        if existing != content:
            print(f"{display(output)} is out of date.", file=sys.stderr)
            return 1
        print(f"{display(output)} is up to date.")
        return 0

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(content, encoding="utf-8")
    print(f"wrote {display(output)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
