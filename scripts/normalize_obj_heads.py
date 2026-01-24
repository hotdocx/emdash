#!/usr/bin/env python3
from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


SKIP_COMMAND_HEADS = {
    "rule",
    "unif_rule",
}


@dataclass(frozen=True)
class Span:
    start: int
    end: int


def is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in {"_", "'", "’"}


def read_file(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_file(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def strip_leading_space(s: str) -> str:
    i = 0
    while i < len(s) and s[i].isspace():
        i += 1
    return s[i:]


def maybe_rewrite_obj_application(inside: str) -> str | None:
    s = strip_leading_space(inside)

    def repl(old: str, new: str) -> str | None:
        if s.startswith(old) and (len(s) == len(old) or s[len(old)].isspace() or s[len(old)] == "("):
            return new + s[len(old) :]
        return None

    # Prefer preserving explicitness: if the source head is explicit via '@', keep it explicit.
    # (Stable heads accept explicit args via '@' as usual.)
    return (
        repl("@Hom_cat", "@Hom")
        or repl("Functor_cat", "Functor")
        or repl("StrictFunctor_cat", "StrictFunctor")
        or repl("@Functord_cat", "@Functord")
        or repl("Functord_cat", "Functord")
        or repl("@Fibre_cat", "@FibreObj")
        or repl("Fibre_cat", "FibreObj")
        or repl("@Transf_cat", "@Transf")
        or repl("Transf_cat", "Transf")
        or repl("@Transfd_cat", "@Transfd")
        or repl("Transfd_cat", "Transfd")
    )


def find_matching_paren(text: str, open_pos: int) -> int | None:
    if open_pos >= len(text) or text[open_pos] != "(":
        return None
    depth = 0
    i = open_pos
    while i < len(text):
        ch = text[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def iter_code_spans(text: str) -> list[Span]:
    """
    Return spans of text that are not in comments (// or /* ... */).
    Handles nested block comments. Strings are treated as code.
    """
    spans: list[Span] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    seg_start: int | None = 0

    def end_segment(at: int) -> None:
        nonlocal seg_start
        if seg_start is not None and seg_start < at:
            spans.append(Span(seg_start, at))
        seg_start = None

    def start_segment(at: int) -> None:
        nonlocal seg_start
        if seg_start is None:
            seg_start = at

    while i < len(text):
        if in_line_comment:
            if text[i] == "\n":
                in_line_comment = False
                start_segment(i + 1)
            i += 1
            continue

        if block_depth > 0:
            if text.startswith("/*", i):
                block_depth += 1
                i += 2
                continue
            if text.startswith("*/", i):
                block_depth -= 1
                i += 2
                if block_depth == 0:
                    start_segment(i)
                continue
            i += 1
            continue

        # We are in code.
        if text.startswith("//", i):
            end_segment(i)
            in_line_comment = True
            i += 2
            continue
        if text.startswith("/*", i):
            end_segment(i)
            block_depth = 1
            i += 2
            continue

        i += 1

    if not in_line_comment and block_depth == 0 and seg_start is not None:
        end_segment(len(text))
    return spans


def build_skip_mask_for_commands(text: str) -> list[Span]:
    """
    Build spans for commands we must not rewrite inside:
    - `rule ... ;`
    - `unif_rule ... ;`
    """
    spans: list[Span] = []
    i = 0
    while i < len(text):
        line_start = i
        nl = text.find("\n", i)
        if nl == -1:
            nl = len(text)
        line = text[line_start:nl]
        stripped = line.lstrip()
        head = stripped.split(None, 1)[0] if stripped else ""
        if head in SKIP_COMMAND_HEADS:
            # Command spans until the next ';' outside comments is hard;
            # we conservatively span until the first ';' on any subsequent line.
            # (This matches the typical style in this repo for rules/unif_rules.)
            cmd_start = line_start + (len(line) - len(stripped))
            j = nl
            semi = text.find(";", cmd_start)
            if semi != -1:
                spans.append(Span(cmd_start, semi + 1))
                i = semi + 1
                continue
        i = nl + 1
    return spans


def in_any_span(pos: int, spans: list[Span]) -> bool:
    for sp in spans:
        if sp.start <= pos < sp.end:
            return True
    return False


def rewrite_text(text: str) -> tuple[str, int]:
    code_spans = iter_code_spans(text)
    skip_spans = build_skip_mask_for_commands(text)

    out: list[str] = []
    i = 0
    rewrites = 0

    while i < len(text):
        if not in_any_span(i, code_spans) or in_any_span(i, skip_spans):
            out.append(text[i])
            i += 1
            continue

        # Avoid breaking stable-head definitions: keep `≔ Obj ( ... )` untouched.
        if text.startswith("≔ Obj (", i):
            out.append("≔ Obj (")
            i += len("≔ Obj (")
            continue

        if text.startswith("Obj", i) and (i == 0 or not is_ident_char(text[i - 1])):
            j = i + 3
            if j < len(text) and not is_ident_char(text[j]):
                while j < len(text) and text[j].isspace():
                    j += 1
                if j < len(text) and text[j] == "(":
                    close = find_matching_paren(text, j)
                    if close is not None:
                        inside = text[j + 1 : close]
                        replaced_inside = maybe_rewrite_obj_application(inside)
                        if replaced_inside is not None:
                            out.append(replaced_inside)
                            rewrites += 1
                            i = close + 1
                            continue

        out.append(text[i])
        i += 1

    return ("".join(out), rewrites)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Normalize `Obj(<K_cat ...>)` to stable Grpd heads (e.g. `Functor ...`, `@Hom ...`)."
    )
    ap.add_argument(
        "path",
        type=Path,
        nargs="?",
        default=Path("emdash2.lp"),
        help="Path to the .lp file to rewrite (default: emdash2.lp).",
    )
    ap.add_argument(
        "--check",
        action="store_true",
        help="Do not write; exit 1 if changes would be made.",
    )
    args = ap.parse_args()

    path: Path = args.path
    before = read_file(path)
    after, n = rewrite_text(before)
    if after == before:
        print(f"{path}: no changes.")
        return 0

    if args.check:
        print(f"{path}: would rewrite {n} occurrence(s).")
        return 1

    write_file(path, after)
    print(f"{path}: rewrote {n} occurrence(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

