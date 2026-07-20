#!/usr/bin/env python3
"""Check book Markdown for semantic math/source-mode mistakes.

The browser renderer correctly preserves Markdown code spans, so TeX placed
inside one is a source error even when the surrounding page renders cleanly.
Likewise, a missing backslash before a TeX control word is usually valid input
to KaTeX but produces a row of italic variables.  This checker owns those two
semantic boundaries; the companion Node check owns strict KaTeX parsing.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MANIFEST = REPO_ROOT / "book" / "book.json"
TEX_COMMAND_RE = re.compile(r"\\[A-Za-z]+")
SUSPICIOUS_BARE_MATH_WORD_RE = re.compile(
    r"(?<!\\)\b(?:"
    r"qquad|quad|longrightarrow|mathsf|operatorname|mathrm|mathbf|"
    r"mathbb|mathcal|equiv|vdash|leadsto|ldots|circ"
    r")\b"
)
FENCE_RE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")


@dataclass(frozen=True)
class Issue:
    file: str
    line: int
    kind: str
    message: str


@dataclass(frozen=True)
class MathSpan:
    file: str
    line: int
    display: bool
    latex: str


def _mask_range(chars: list[str], start: int, end: int) -> None:
    for index in range(start, end):
        if chars[index] not in "\r\n":
            chars[index] = " "


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _is_escaped(text: str, offset: int) -> bool:
    backslashes = 0
    cursor = offset - 1
    while cursor >= 0 and text[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return backslashes % 2 == 1


def _mask_fenced_code(text: str) -> tuple[str, list[Issue]]:
    chars = list(text)
    issues: list[Issue] = []
    offset = 0
    fence_character: str | None = None
    fence_length = 0
    fence_line = 0

    for line_number, line in enumerate(text.splitlines(keepends=True), start=1):
        match = FENCE_RE.match(line.rstrip("\r\n"))
        if fence_character is None:
            if match:
                marker = match.group(1)
                fence_character = marker[0]
                fence_length = len(marker)
                fence_line = line_number
                _mask_range(chars, offset, offset + len(line))
        else:
            _mask_range(chars, offset, offset + len(line))
            if match:
                marker = match.group(1)
                remainder = match.group(2)
                if (
                    marker[0] == fence_character
                    and len(marker) >= fence_length
                    and remainder.strip() == ""
                ):
                    fence_character = None
                    fence_length = 0
                    fence_line = 0
        offset += len(line)

    if fence_character is not None:
        issues.append(
            Issue("", fence_line, "unclosed-fence", "fenced code block is not closed")
        )
    return "".join(chars), issues


def _inline_code_spans(text: str) -> list[tuple[int, int, str]]:
    spans: list[tuple[int, int, str]] = []
    line_start = 0
    for line in text.splitlines(keepends=True):
        content_end = len(line.rstrip("\r\n"))
        cursor = 0
        while cursor < content_end:
            if line[cursor] != "`":
                cursor += 1
                continue
            run_end = cursor + 1
            while run_end < content_end and line[run_end] == "`":
                run_end += 1
            marker = line[cursor:run_end]
            closing = line.find(marker, run_end, content_end)
            while closing >= 0:
                before_is_tick = closing > 0 and line[closing - 1] == "`"
                after = closing + len(marker)
                after_is_tick = after < content_end and line[after] == "`"
                if not before_is_tick and not after_is_tick:
                    break
                closing = line.find(marker, closing + 1, content_end)
            if closing < 0:
                cursor = run_end
                continue
            spans.append(
                (
                    line_start + cursor,
                    line_start + closing + len(marker),
                    line[run_end:closing],
                )
            )
            cursor = closing + len(marker)
        line_start += len(line)
    return spans


def _math_spans(text: str) -> tuple[list[MathSpan], list[Issue], str]:
    spans: list[MathSpan] = []
    issues: list[Issue] = []
    chars = list(text)
    cursor = 0
    while cursor < len(text):
        if text[cursor] != "$" or _is_escaped(text, cursor):
            cursor += 1
            continue
        display = text.startswith("$$", cursor)
        marker = "$$" if display else "$"
        body_start = cursor + len(marker)
        search = body_start
        closing = -1
        while search < len(text):
            candidate = text.find(marker, search)
            if candidate < 0:
                break
            if not display and "\n" in text[body_start:candidate]:
                break
            if not _is_escaped(text, candidate):
                closing = candidate
                break
            search = candidate + len(marker)
        if closing < 0:
            issues.append(
                Issue(
                    "",
                    _line_number(text, cursor),
                    "unclosed-math",
                    "math delimiter " + marker + " is not closed",
                )
            )
            cursor += len(marker)
            continue
        body = text[body_start:closing]
        spans.append(
            MathSpan(
                "",
                _line_number(text, cursor),
                display,
                body.strip(),
            )
        )
        _mask_range(chars, cursor, closing + len(marker))
        cursor = closing + len(marker)
    return spans, issues, "".join(chars)


def scan_markdown(text: str, relative: str) -> tuple[list[Issue], list[MathSpan]]:
    without_fences, issues = _mask_fenced_code(text)
    issues = [Issue(relative, item.line, item.kind, item.message) for item in issues]
    chars = list(without_fences)

    for start, end, content in _inline_code_spans(without_fences):
        command = TEX_COMMAND_RE.search(content)
        if command:
            issues.append(
                Issue(
                    relative,
                    _line_number(text, start),
                    "tex-in-code-span",
                    "TeX command " + repr(command.group(0)) +
                    " is literal inside a Markdown code span",
                )
            )
        _mask_range(chars, start, end)

    math, math_issues, prose = _math_spans("".join(chars))
    issues.extend(
        Issue(relative, item.line, item.kind, item.message) for item in math_issues
    )
    math = [MathSpan(relative, item.line, item.display, item.latex) for item in math]

    for span in math:
        bare = SUSPICIOUS_BARE_MATH_WORD_RE.search(span.latex)
        if bare:
            issues.append(
                Issue(
                    relative,
                    span.line,
                    "bare-tex-control-word",
                    "suspicious bare TeX control word " + repr(bare.group(0)) +
                    " inside math",
                )
            )

    for command in TEX_COMMAND_RE.finditer(prose):
        issues.append(
            Issue(
                relative,
                _line_number(text, command.start()),
                "tex-in-prose",
                "TeX command " + repr(command.group(0)) +
                " is outside a math span",
            )
        )

    return issues, math


def _load_sources(manifest_path: Path) -> list[tuple[str, Path]]:
    manifest_path = manifest_path.resolve()
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    sources = manifest.get("sources")
    if not isinstance(sources, list) or not sources:
        raise ValueError(f"{manifest_path}: sources must be a non-empty array")
    loaded: list[tuple[str, Path]] = []
    for index, source in enumerate(sources):
        raw = source.get("path") if isinstance(source, dict) else None
        if not isinstance(raw, str) or not raw:
            raise ValueError(f"{manifest_path}: sources[{index}].path is invalid")
        candidate = (REPO_ROOT / raw).resolve()
        try:
            candidate.relative_to(REPO_ROOT)
        except ValueError as error:
            raise ValueError(f"{manifest_path}: source escapes repository: {raw}") from error
        if not candidate.is_file():
            raise ValueError(f"{manifest_path}: source is missing: {raw}")
        loaded.append((candidate.relative_to(REPO_ROOT).as_posix(), candidate))
    return loaded


def check_manifest(manifest_path: Path) -> tuple[list[Issue], list[MathSpan], int]:
    issues: list[Issue] = []
    math: list[MathSpan] = []
    sources = _load_sources(manifest_path)
    for relative, source in sources:
        source_issues, source_math = scan_markdown(
            source.read_text(encoding="utf-8"), relative
        )
        issues.extend(source_issues)
        math.extend(source_math)
    return issues, math, len(sources)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--math-json",
        action="store_true",
        help="emit source diagnostics and extracted math spans as JSON",
    )
    args = parser.parse_args(argv)
    try:
        issues, math, source_count = check_manifest(args.manifest)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"book typography check failed: {error}", file=sys.stderr)
        return 1

    if args.math_json:
        print(
            json.dumps(
                {
                    "issues": [asdict(item) for item in issues],
                    "math": [asdict(item) for item in math],
                    "sourceCount": source_count,
                },
                ensure_ascii=False,
            )
        )
        return 0

    if issues:
        for item in issues:
            print(
                f"{item.file}:{item.line}: {item.kind}: {item.message}",
                file=sys.stderr,
            )
        return 1
    print(
        f"book typography check passed: {source_count} source file(s), "
        f"{len(math)} math span(s)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
