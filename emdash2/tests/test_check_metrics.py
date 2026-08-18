from __future__ import annotations

import unittest
from tempfile import TemporaryDirectory
from pathlib import Path

from scripts.check_metrics import (
    CheckResult,
    check_content_snapshot,
    check_execution_order,
    format_report,
    load_resume_checks,
    report_check_content_snapshot,
    report_snapshot_issue,
    report_source_metrics_snapshot,
    source_metrics_snapshot,
    write_resume_checks,
)


class CheckMetricsTests(unittest.TestCase):
    def test_near_timeout_checks_run_first_without_reordering_report_inputs(self) -> None:
        files = [
            Path("emdash3_2.lp"),
            Path("emdash3_2_commutative_algebra_affine_glue.lp"),
            Path("emdash3_2_checks.lp"),
            Path("examples/example.lp"),
        ]
        original = list(files)
        self.assertEqual(
            check_execution_order(files),
            [
                Path("emdash3_2_checks.lp"),
                Path("emdash3_2_commutative_algebra_affine_glue.lp"),
                Path("emdash3_2.lp"),
                Path("examples/example.lp"),
            ],
        )
        self.assertEqual(files, original)

    def test_snapshot_changes_with_reported_source_metrics(self) -> None:
        before = {"emdash3_2.lp": {"lines": 10, "sections": {"0. Core": 10}}}
        after = {"emdash3_2.lp": {"lines": 11, "sections": {"0. Core": 11}}}
        self.assertNotEqual(
            source_metrics_snapshot(before), source_metrics_snapshot(after)
        )

    def test_content_snapshot_changes_when_metrics_can_stay_equal(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "same_metrics.lp"
            source.write_text("symbol left : TYPE;\n", encoding="utf-8")
            before = check_content_snapshot([Path("same_metrics.lp")], root)
            source.write_text("symbol rite : TYPE;\n", encoding="utf-8")
            after = check_content_snapshot([Path("same_metrics.lp")], root)
        self.assertNotEqual(before, after)

    def test_resume_state_requires_exact_identity_and_keeps_only_successes(self) -> None:
        identity = {"state_version": 1, "content_snapshot": "a" * 64}
        checks = {
            "ok.lp": CheckResult("ok.lp", 0, 1.25),
            "failed.lp": CheckResult("failed.lp", 124, 60.0),
        }
        with TemporaryDirectory() as directory:
            state = Path(directory) / "state.json"
            write_resume_checks(state, identity, checks)
            resumed = load_resume_checks(state, identity)
            stale = load_resume_checks(
                state,
                {"state_version": 1, "content_snapshot": "b" * 64},
            )
        self.assertEqual(list(resumed), ["ok.lp"])
        self.assertEqual(resumed["ok.lp"].evidence, "resumed")
        self.assertEqual(stale, {})

    def test_resume_state_reuses_unchanged_subset_after_additive_extension(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            old_source = root / "old.lp"
            new_source = root / "new.lp"
            old_source.write_text("symbol old : TYPE;\n", encoding="utf-8")
            new_source.write_text("symbol new : TYPE;\n", encoding="utf-8")
            shared = {
                "state_version": 1,
                "lambdapi_version": "test",
                "timeout": "90s",
                "warnings_enabled": False,
                "extra_lambdapi_flags": "",
            }
            previous = {
                **shared,
                "files": ["old.lp"],
                "content_snapshot": check_content_snapshot(
                    [Path("old.lp")], root
                ),
            }
            current = {
                **shared,
                "files": ["old.lp", "new.lp"],
                "content_snapshot": check_content_snapshot(
                    [Path("old.lp"), Path("new.lp")], root
                ),
            }
            state = root / "state.json"
            write_resume_checks(
                state,
                previous,
                {
                    "old.lp": CheckResult("old.lp", 0, 1.25),
                    "new.lp": CheckResult("new.lp", 0, 9.99),
                },
            )

            resumed = load_resume_checks(state, current, root)
            old_source.write_text("symbol changed : TYPE;\n", encoding="utf-8")
            stale = load_resume_checks(state, current, root)

        self.assertEqual(list(resumed), ["old.lp"])
        self.assertEqual(resumed["old.lp"].evidence, "resumed")
        self.assertEqual(stale, {})

    def test_snapshot_is_independent_of_timings_and_generation_date(self) -> None:
        files = {
            "emdash3_2.lp": {
                "lines": 10,
                "nonblank_lines": 9,
                "comment_lines": 1,
                "symbols": 1,
                "rules": 1,
                "unif_rules": 0,
                "asserts": 0,
                "todos": 0,
                "deferred_mentions": 0,
                "sections": {"0. Core": 10},
            }
        }
        snapshot = source_metrics_snapshot(files)
        base = {
            "generated_at": "2026-07-22T00:00:00-0400",
            "lambdapi_version": "test",
            "timeout": "60s",
            "warnings_enabled": False,
            "extra_lambdapi_flags": "",
            "checks": [
                {"file": "emdash3_2.lp", "returncode": 0, "duration_s": 1.0}
            ],
            "files": files,
            "example_files": [],
            "source_metrics_snapshot": snapshot,
            "check_content_snapshot": "c" * 64,
        }
        later = dict(base)
        later["generated_at"] = "2026-07-23T00:00:00-0400"
        later["checks"] = [
            {"file": "emdash3_2.lp", "returncode": 0, "duration_s": 99.0}
        ]
        self.assertEqual(
            report_source_metrics_snapshot(format_report(base)),
            report_source_metrics_snapshot(format_report(later)),
        )

    def test_report_snapshot_accepts_matching_digest(self) -> None:
        digest = "a" * 64
        content = "b" * 64
        report = (
            f"- Source-metrics snapshot: `sha256:{digest}`\n"
            f"- Check-content snapshot: `sha256:{content}`\n"
        )
        self.assertEqual(report_check_content_snapshot(report), content)
        self.assertIsNone(report_snapshot_issue(digest, report, content))

    def test_report_snapshot_rejects_missing_or_stale_digest(self) -> None:
        current = "b" * 64
        stale = "a" * 64
        self.assertEqual(
            report_snapshot_issue(current, "# Health\n"),
            "health report has no source-metrics snapshot",
        )
        self.assertEqual(
            report_snapshot_issue(
                current,
                f"- Source-metrics snapshot: `sha256:{stale}`\n",
            ),
            "health report source metrics are stale: "
            f"recorded sha256:{stale}, current sha256:{current}",
        )
        matching_metrics = f"- Source-metrics snapshot: `sha256:{current}`\n"
        self.assertEqual(
            report_snapshot_issue(current, matching_metrics, current),
            "health report has no check-content snapshot",
        )
        self.assertEqual(
            report_snapshot_issue(
                current,
                matching_metrics
                + f"- Check-content snapshot: `sha256:{stale}`\n",
                current,
            ),
            "health report checked contents are stale: "
            f"recorded sha256:{stale}, current sha256:{current}",
        )


if __name__ == "__main__":
    unittest.main()
