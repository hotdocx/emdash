#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


SKIP_COMMAND_HEADS = {
    "rule",
    "unif_rule",
}


# Phase A (very safe, observed in emdash2.lp)
ALLOW_BRACKET_HEADS_PHASE_A = {
    "tapp1_int_fapp0_transf",
    "tdapp1_int_fapp0_transfd",
    "Total_func",
    "op_val_func",
    "prodFib_func_func",
}


# Phase B (bigger win): stable-head “@K …” -> “K …” dropping obvious indices.
ALLOW_AT_REWRITES_PHASE_B: dict[str, int] = {
    "@Functord": 1,  # @Functord B E D -> Functord E D
    "@FibreObj": 1,  # @FibreObj B E X -> FibreObj E X
    "@Transf": 2,  # @Transf A B F G -> Transf F G
    "@Transfd": 3,  # @Transfd Z E D FF GG -> Transfd FF GG
}


STABLE_HEADS = {
    "Hom",
    "Functor",
    "StrictFunctor",
    "Functord",
    "FibreObj",
    "Transf",
    "Transfd",
}


@dataclass(frozen=True)
class Span:
    start: int
    end: int


def read_file(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_file(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in {"_", "'", "’", "@"}


def iter_code_spans(text: str) -> list[Span]:
    """
    Return spans of text that are not in comments (// or /* ... */).
    Handles nested block comments.
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


def build_skip_spans_for_commands(text: str) -> list[Span]:
    """
    Build spans for commands we must not rewrite inside:
    - `rule ... ;`
    - `unif_rule ... ;`

    Heuristic: span from the command head to the next ';'.
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
            cmd_start = line_start + (len(line) - len(stripped))
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


def find_matching(text: str, open_pos: int, open_ch: str, close_ch: str) -> int | None:
    if open_pos >= len(text) or text[open_pos] != open_ch:
        return None
    depth = 0
    i = open_pos
    while i < len(text):
        ch = text[i]
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def consume_term(text: str, pos: int) -> tuple[str, int] | None:
    """
    Consume one term argument at `pos` (skipping whitespace), returning (term_text, next_pos).
    Conservative: supports identifiers and balanced (...) / [...] terms.
    """
    i = pos
    while i < len(text) and text[i].isspace():
        i += 1
    if i >= len(text):
        return None

    ch = text[i]
    if ch == "(":
        close = find_matching(text, i, "(", ")")
        if close is None:
            return None
        return (text[i : close + 1], close + 1)

    if ch == "[":
        close = find_matching(text, i, "[", "]")
        if close is None:
            return None
        return (text[i : close + 1], close + 1)

    # identifier-ish token (approximate; adequate for our local rewrites)
    j = i
    while j < len(text) and not text[j].isspace() and text[j] not in {"(", ")", "[", "]", ",", ";"}:
        j += 1
    if j == i:
        return None
    return (text[i:j], j)


def collect_declared_symbols(text: str) -> set[str]:
    sym: set[str] = set()
    for line in text.splitlines():
        m = re.match(
            r"\s*(?:constant\s+|injective\s+|opaque\s+|private\s+|protected\s+|sequential\s+)*symbol\s+(@?[A-Za-z_][A-Za-z0-9_']*)\b",
            line,
        )
        if m:
            sym.add(m.group(1))
    return sym


def remove_explicit_brackets_after_head(
    text: str,
    i: int,
    head: str,
    allowed_heads: set[str],
    declared: set[str],
) -> tuple[str, int, int] | None:
    """
    If at position i we have <head> followed by one or more explicit implicit args `[ ... ]`
    (with no ':' inside), remove those `[ ... ]` blocks.
    """
    if head not in allowed_heads:
        return None
    if head not in declared:
        return None

    j = i + len(head)
    # allow optional spaces, but also allow direct `head[Z]`
    k = j
    while k < len(text) and text[k].isspace():
        k += 1

    removed_any = False
    removed_count = 0
    pos = k
    while pos < len(text) and text[pos] == "[":
        close = find_matching(text, pos, "[", "]")
        if close is None:
            break
        content = text[pos + 1 : close]
        # Only remove explicit instantiations: reject binder-like brackets containing ':'.
        if ":" in content:
            break
        removed_any = True
        removed_count += 1
        pos = close + 1
        # swallow whitespace between consecutive bracket args
        while pos < len(text) and text[pos].isspace():
            pos += 1

    if not removed_any:
        return None

    # produce replacement: keep a single space if there was whitespace before the first bracket
    # and the next char is not whitespace/punct requiring no space.
    replacement = head
    next_pos = pos
    # If we consumed at least one whitespace before the first bracket, keep one space (cosmetic).
    if k > j and next_pos < len(text) and not text[next_pos].isspace() and text[next_pos] not in {")", "]", ";", ","}:
        replacement += " "
    return (replacement, next_pos, removed_count)


def rewrite_at_head_application(
    text: str,
    i: int,
    head: str,
    drop_n: int,
    declared: set[str],
) -> tuple[str, int] | None:
    """
    Rewrite `@K a1 ... an ...` -> `K a(drop_n+1) ...` by consuming enough args.
    Only used for a small allowlist of stable heads (phase B).
    """
    # `@K` is syntactic “disable implicits” for symbol `K`.
    if head.startswith("@"):
        if head[1:] not in declared:
            return None
    elif head not in declared:
        return None

    pos = i + len(head)
    args: list[str] = []
    for _ in range(drop_n + 1):  # need at least drop_n args, plus one to keep
        t = consume_term(text, pos)
        if t is None:
            return None
        term, pos = t
        args.append(term.strip())

    # Now consume remaining args needed by the head kind:
    # @Hom needs 3 args total; @Functord 3; @FibreObj 3; @Transf 4; @Transfd 5.
    needed_total = {
        "@Functord": 3,
        "@FibreObj": 3,
        "@Transf": 4,
        "@Transfd": 5,
    }.get(head)
    if needed_total is None:
        return None
    while len(args) < needed_total:
        t = consume_term(text, pos)
        if t is None:
            return None
        term, pos = t
        args.append(term.strip())

    kept = args[drop_n:]
    new_head = head[1:]  # drop leading '@'
    replacement = new_head + " " + " ".join(kept)
    return (replacement, pos)


def rewrite_text(text: str, phase_b: bool) -> tuple[str, dict[str, int]]:
    declared = collect_declared_symbols(text)
    code_spans = iter_code_spans(text)
    skip_spans = build_skip_spans_for_commands(text)

    allowed_bracket_heads = set(ALLOW_BRACKET_HEADS_PHASE_A)
    if phase_b:
        allowed_bracket_heads |= STABLE_HEADS

    stats: dict[str, int] = {
        "bracket_groups_removed": 0,
        "at_head_rewrites": 0,
    }

    out: list[str] = []
    i = 0
    while i < len(text):
        if not in_any_span(i, code_spans) or in_any_span(i, skip_spans):
            out.append(text[i])
            i += 1
            continue

        # Try bracket-group removal for allowed symbol heads.
        if (i == 0 or not is_ident_char(text[i - 1])) and (text[i].isalpha() or text[i] in {"@", "_"}):
            # read a plausible head token
            j = i
            while j < len(text) and is_ident_char(text[j]):
                j += 1
            head = text[i:j]
            if head:
                r = remove_explicit_brackets_after_head(text, i, head, allowed_bracket_heads, declared)
                if r is not None:
                    rep, next_pos, removed = r
                    out.append(rep)
                    stats["bracket_groups_removed"] += removed
                    i = next_pos
                    continue

        # Phase B: rewrite @StableHead applications to StableHead dropping index args.
        if phase_b:
            for at_head, drop_n in ALLOW_AT_REWRITES_PHASE_B.items():
                if (
                    text.startswith(at_head, i)
                    and (i == 0 or not is_ident_char(text[i - 1]))
                    and (i + len(at_head) >= len(text) or not is_ident_char(text[i + len(at_head)]))
                ):
                    r2 = rewrite_at_head_application(text, i, at_head, drop_n, declared)
                    if r2 is not None:
                        rep, next_pos = r2
                        out.append(rep)
                        stats["at_head_rewrites"] += 1
                        i = next_pos
                        continue
            # fallthrough

        out.append(text[i])
        i += 1

    return ("".join(out), stats)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Reduce explicit implicit-argument noise in term contexts (skips rule/unif_rule and comments)."
    )
    ap.add_argument(
        "path",
        type=Path,
        nargs="?",
        default=Path("emdash2.lp"),
        help="Path to the .lp file to rewrite (default: emdash2.lp).",
    )
    ap.add_argument(
        "--phase-b",
        action="store_true",
        help="Also rewrite stable heads: `@Hom A X Y` -> `Hom X Y`, etc.",
    )
    ap.add_argument(
        "--check",
        action="store_true",
        help="Do not write; exit 1 if changes would be made.",
    )
    args = ap.parse_args()

    path: Path = args.path
    before = read_file(path)
    after, stats = rewrite_text(before, phase_b=args.phase_b)
    if after == before:
        print(f"{path}: no changes.")
        return 0

    if args.check:
        print(f"{path}: would change file. Stats={stats}")
        return 1

    write_file(path, after)
    print(f"{path}: updated. Stats={stats}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
