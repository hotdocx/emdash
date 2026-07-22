from __future__ import annotations

import unittest

from scripts.check_book_evidence import main, reference_role_issue


class BookEvidenceTests(unittest.TestCase):
    def test_active_owner_module_is_allowed(self) -> None:
        self.assertIsNone(reference_role_issue("emdash3_2.lp", owner=True))

    def test_report_cannot_be_an_implementation_owner(self) -> None:
        self.assertEqual(
            reference_role_issue("reports/EMDASH_FOUNDATIONS.md", owner=True),
            "owner must be an active Lambdapi module, got "
            "reports/EMDASH_FOUNDATIONS.md",
        )

    def test_diagnostics_and_examples_are_reviewer_surfaces(self) -> None:
        self.assertIsNone(
            reference_role_issue("emdash3_2_checks.lp", owner=False)
        )
        self.assertIsNone(
            reference_role_issue("examples/path_category.lp", owner=False)
        )

    def test_implementation_module_cannot_self_review(self) -> None:
        self.assertEqual(
            reference_role_issue("emdash3_2.lp", owner=False),
            "reviewer must be emdash3_2_checks.lp or a reviewer example, "
            "got emdash3_2.lp",
        )

    def test_current_book_evidence_register_satisfies_policy(self) -> None:
        self.assertEqual(main(), 0)


if __name__ == "__main__":
    unittest.main()
