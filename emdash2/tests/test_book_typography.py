from __future__ import annotations

import unittest
from pathlib import Path

from scripts.check_book_typography import REPO_ROOT, check_manifest, scan_markdown


FIXTURES = REPO_ROOT / "tests" / "fixtures" / "book_typography"


class BookTypographyTests(unittest.TestCase):
    def scan_fixture(self, name: str):
        path = FIXTURES / name
        return scan_markdown(path.read_text(encoding="utf-8"), path.name)

    def test_valid_math_and_literal_fenced_code(self) -> None:
        issues, math = self.scan_fixture("valid.md")
        self.assertEqual(issues, [])
        self.assertEqual(len(math), 2)

    def test_tex_command_in_inline_code_is_rejected(self) -> None:
        issues, _ = self.scan_fixture("tex-in-code-span.md")
        self.assertEqual([item.kind for item in issues], ["tex-in-code-span"])

    def test_bare_control_word_in_math_is_rejected(self) -> None:
        issues, _ = self.scan_fixture("bare-control-word.md")
        self.assertEqual([item.kind for item in issues], ["bare-tex-control-word"])

    def test_tex_command_in_prose_is_rejected(self) -> None:
        issues, _ = self.scan_fixture("tex-in-prose.md")
        self.assertEqual([item.kind for item in issues], ["tex-in-prose"])

    def test_current_manifest_is_clean(self) -> None:
        issues, math, source_count = check_manifest(REPO_ROOT / "book" / "book.json")
        self.assertEqual(issues, [])
        self.assertGreater(len(math), 0)
        self.assertGreater(source_count, 0)


if __name__ == "__main__":
    unittest.main()
