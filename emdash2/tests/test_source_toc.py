from __future__ import annotations

import unittest

from scripts.check_source_toc import (
    SOURCE,
    SOURCE_ENTRY,
    entries,
    heading_structure_issues,
)


class SourceTocTests(unittest.TestCase):
    def test_current_source_heading_structure_is_valid(self) -> None:
        source = entries(
            SOURCE.read_text(encoding="utf-8").splitlines(), SOURCE_ENTRY
        )
        self.assertEqual(heading_structure_issues(source), [])

    def test_missing_subsection_is_rejected(self) -> None:
        headings = [
            ("5", "Products"),
            ("5a", "Formation"),
            ("5b", "Maps"),
            ("5d", "Telescope"),
        ]
        self.assertEqual(
            heading_structure_issues(headings),
            ["subsection 5d is nonsequential; expected 5c"],
        )

    def test_reserved_terminal_bridge_is_allowed(self) -> None:
        headings = [
            ("18", "Profunctors"),
            ("18a", "Core"),
            ("18b", "Tensor"),
            ("18z", "Late bridges"),
        ]
        self.assertEqual(heading_structure_issues(headings), [])

    def test_heading_after_terminal_bridge_is_rejected(self) -> None:
        headings = [
            ("18", "Profunctors"),
            ("18a", "Core"),
            ("18z", "Late bridges"),
            ("18b", "Too late"),
        ]
        self.assertEqual(
            heading_structure_issues(headings),
            ["subsection 18b follows reserved terminal subsection"],
        )

    def test_subsection_requires_its_parent(self) -> None:
        headings = [("5", "Products"), ("6a", "Wrong parent")]
        self.assertEqual(
            heading_structure_issues(headings),
            ["subsection 6a is under section 5, expected parent section 6"],
        )


if __name__ == "__main__":
    unittest.main()
