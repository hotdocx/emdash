from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.lint_report_headers import (
    INDEX,
    REPORTS_ROOT,
    header_fields,
    registry_issues,
)


class ReportRegistryTests(unittest.TestCase):
    def write_plan(
        self,
        root: Path,
        name: str,
        status: str,
        *,
        omit: str | None = None,
    ) -> None:
        fields = {
            "Plan-ID": f"PLAN-{name}",
            "Depends-On": "active source",
            "Supersedes": "no prior plan",
            "Side-Task-Ledger": "TEST-0",
            "Infinity-Codex-Origin": "test fixture",
            "Infinity-Codex-Decision-Responses": "test decision",
            "Status": status,
        }
        text = "# Fixture\n\n" + "\n\n".join(
            f"{field}: {value}"
            for field, value in fields.items()
            if field != omit
        )
        (root / name).write_text(text + "\n", encoding="utf-8")

    def index_text(
        self,
        *,
        active: list[str] | None = None,
        completed: list[str] | None = None,
        deferred: list[str] | None = None,
        superseded: list[str] | None = None,
    ) -> str:
        sections = [
            ("Active Plans", active or []),
            ("Completed Current-Architecture Ledgers", completed or []),
            ("Deferred Proposals", deferred or []),
            ("Superseded Or Historical Plans", superseded or []),
        ]
        return "".join(
            f"## {heading}\n\n"
            + "".join(f"- `{name}`:\n  fixture\n" for name in names)
            + "\n"
            for heading, names in sections
        )

    def test_live_registry_is_valid(self) -> None:
        self.assertEqual(
            registry_issues(INDEX.read_text(encoding="utf-8"), REPORTS_ROOT),
            [],
        )

    def test_all_four_valid_lifecycles_are_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_plan(root, "active.md", "active implementation plan")
            self.write_plan(root, "complete.md", "completed implementation plan")
            self.write_plan(root, "deferred.md", "proposed implementation plan")
            self.write_plan(root, "old.md", "superseded historical plan")
            index = self.index_text(
                active=["active.md"],
                completed=["complete.md"],
                deferred=["deferred.md"],
                superseded=["old.md"],
            )
            self.assertEqual(registry_issues(index, root), [])

    def test_completed_plan_is_rejected_from_active_section(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_plan(root, "done.md", "completed implementation plan")
            issues = registry_issues(self.index_text(active=["done.md"]), root)
            self.assertTrue(any("completed/closed status" in issue for issue in issues))

    def test_superseded_plan_is_rejected_from_active_section(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_plan(root, "old.md", "superseded by PLAN-NEXT")
            issues = registry_issues(self.index_text(active=["old.md"]), root)
            self.assertTrue(any("superseded status" in issue for issue in issues))

    def test_duplicate_lifecycle_registration_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_plan(root, "plan.md", "active implementation plan")
            issues = registry_issues(
                self.index_text(active=["plan.md"], completed=["plan.md"]),
                root,
            )
            self.assertTrue(any("registered in both" in issue for issue in issues))

    def test_missing_registered_file_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            issues = registry_issues(
                self.index_text(active=["missing.md"]),
                root,
            )
            self.assertTrue(
                any("listed in reports/INDEX.md but missing" in issue for issue in issues)
            )

    def test_missing_required_header_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_plan(
                root,
                "plan.md",
                "active implementation plan",
                omit="Depends-On",
            )
            issues = registry_issues(self.index_text(active=["plan.md"]), root)
            self.assertTrue(any("missing Depends-On" in issue for issue in issues))

    def test_wrapped_status_field_is_read_completely(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plan.md"
            self.write_plan(path.parent, path.name, "active implementation\ncontinuation")
            self.assertEqual(
                header_fields(path)["Status"],
                "active implementation continuation",
            )


if __name__ == "__main__":
    unittest.main()
