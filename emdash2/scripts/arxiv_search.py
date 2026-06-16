#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import textwrap
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
API_URL = "https://export.arxiv.org/api/query"
ATOM = "{http://www.w3.org/2005/Atom}"
ARXIV = "{http://arxiv.org/schemas/atom}"


def cache_key(params: dict[str, str]) -> str:
    encoded = urllib.parse.urlencode(sorted(params.items()))
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()[:16]


def fetch(params: dict[str, str], cache_dir: Path, refresh: bool) -> str:
    cache_dir.mkdir(parents=True, exist_ok=True)
    path = cache_dir / f"{cache_key(params)}.xml"
    if path.exists() and not refresh:
        return path.read_text(encoding="utf-8")

    url = f"{API_URL}?{urllib.parse.urlencode(params)}"
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "emdash-mathops/0.1 (arxiv literature search)"},
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        data = response.read().decode("utf-8")
    path.write_text(data, encoding="utf-8")
    return data


def text_of(entry: ET.Element, name: str) -> str:
    value = entry.findtext(f"{ATOM}{name}") or ""
    return " ".join(value.split())


def arxiv_id_from_url(url: str) -> str:
    return url.rstrip("/").split("/")[-1]


def base_arxiv_id(arxiv_id: str) -> str:
    if "v" in arxiv_id:
        head, tail = arxiv_id.rsplit("v", 1)
        if tail.isdigit():
            return head
    return arxiv_id


def parse_entries(xml: str) -> list[dict[str, object]]:
    root = ET.fromstring(xml)
    entries: list[dict[str, object]] = []
    for entry in root.findall(f"{ATOM}entry"):
        abs_url = text_of(entry, "id")
        arxiv_id = arxiv_id_from_url(abs_url)
        primary = entry.find(f"{ARXIV}primary_category")
        categories = [cat.attrib.get("term", "") for cat in entry.findall(f"{ATOM}category")]
        entries.append(
            {
                "id": arxiv_id,
                "base_id": base_arxiv_id(arxiv_id),
                "title": text_of(entry, "title"),
                "summary": text_of(entry, "summary"),
                "published": text_of(entry, "published"),
                "updated": text_of(entry, "updated"),
                "authors": [
                    " ".join((author.findtext(f"{ATOM}name") or "").split())
                    for author in entry.findall(f"{ATOM}author")
                ],
                "primary_category": primary.attrib.get("term", "") if primary is not None else "",
                "categories": [cat for cat in categories if cat],
                "arxiv_url": f"https://arxiv.org/abs/{arxiv_id}",
                "pdf_url": f"https://arxiv.org/pdf/{arxiv_id}",
                "ar5iv_url": f"https://ar5iv.labs.arxiv.org/html/{base_arxiv_id(arxiv_id)}",
            }
        )
    return entries


def format_markdown(entries: list[dict[str, object]], query: str) -> str:
    lines = [
        f"# arXiv search: `{query}`",
        "",
        f"Generated: {time.strftime('%Y-%m-%d %H:%M:%S %z')}",
        "",
    ]
    if not entries:
        lines.append("No results.")
        return "\n".join(lines)

    for i, entry in enumerate(entries, start=1):
        authors = ", ".join(entry["authors"][:5])  # type: ignore[index]
        if len(entry["authors"]) > 5:  # type: ignore[arg-type]
            authors += ", et al."
        categories = ", ".join(entry["categories"])  # type: ignore[arg-type]
        summary = textwrap.shorten(str(entry["summary"]), width=550, placeholder=" ...")
        lines.extend(
            [
                f"## {i}. {entry['title']}",
                "",
                f"- arXiv: [{entry['id']}]({entry['arxiv_url']})",
                f"- ar5iv: [{entry['base_id']}]({entry['ar5iv_url']})",
                f"- PDF: {entry['pdf_url']}",
                f"- Authors: {authors}",
                f"- Published: {entry['published']}",
                f"- Updated: {entry['updated']}",
                f"- Primary category: `{entry['primary_category']}`",
                f"- Categories: `{categories}`",
                "",
                summary,
                "",
            ]
        )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Search arXiv and emit markdown with arXiv/ar5iv links."
    )
    parser.add_argument("--query", required=True, help="arXiv API search_query.")
    parser.add_argument("--max-results", type=int, default=10)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument(
        "--sort",
        choices=["relevance", "lastUpdatedDate", "submittedDate"],
        default="relevance",
    )
    parser.add_argument(
        "--sort-order",
        choices=["ascending", "descending"],
        default="descending",
    )
    parser.add_argument(
        "--cache-dir",
        type=Path,
        default=ROOT / ".cache" / "arxiv",
        help="Cache directory for raw API XML.",
    )
    parser.add_argument("--refresh", action="store_true", help="Ignore cache.")
    parser.add_argument("--output", type=Path, help="Write markdown to a file.")
    args = parser.parse_args()

    params = {
        "search_query": args.query,
        "start": str(args.start),
        "max_results": str(args.max_results),
        "sortBy": args.sort,
        "sortOrder": args.sort_order,
    }
    xml = fetch(params, args.cache_dir, args.refresh)
    markdown = format_markdown(parse_entries(xml), args.query)

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(markdown, encoding="utf-8")
    else:
        print(markdown)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
