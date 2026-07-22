from __future__ import annotations

import unittest

from scripts.check_metrics import (
    format_report,
    report_snapshot_issue,
    report_source_metrics_snapshot,
    source_metrics_snapshot,
)


class CheckMetricsTests(unittest.TestCase):
    def test_snapshot_changes_with_reported_source_metrics(self) -> None:
        before = {"emdash3_2.lp": {"lines": 10, "sections": {"0. Core": 10}}}
        after = {"emdash3_2.lp": {"lines": 11, "sections": {"0. Core": 11}}}
        self.assertNotEqual(
            source_metrics_snapshot(before), source_metrics_snapshot(after)
        )

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
        report = f"- Source-metrics snapshot: `sha256:{digest}`\n"
        self.assertIsNone(report_snapshot_issue(digest, report))

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


if __name__ == "__main__":
    unittest.main()
