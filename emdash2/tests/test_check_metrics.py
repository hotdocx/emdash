from __future__ import annotations

from contextlib import redirect_stdout
from io import StringIO
import re
import unittest
from unittest.mock import call, patch
from tempfile import TemporaryDirectory
from pathlib import Path

from scripts.check_metrics import (
    CheckResult,
    SPECIAL_SNAKE_ROW_CHECK_FILES,
    SPECIAL_SNAKE_TARGET_CYCLE_CHECK_FILES,
    SPECIAL_SNAKE_TARGET_HOMOLOGY_CHECK_FILES,
    check_content_snapshot,
    check_execution_order,
    format_report,
    load_resume_checks,
    report_check_content_snapshot,
    report_snapshot_issue,
    report_source_metrics_snapshot,
    run_checks,
    source_metrics_snapshot,
    write_resume_checks,
)


class CheckMetricsTests(unittest.TestCase):
    @patch("scripts.check_metrics.run_command")
    def test_six_term_join_uses_one_isolated_chain(self, run_command) -> None:
        run_command.side_effect = [(0, "", 1.0), (0, "", 6.0)]
        files = [
            Path("plain.lp"),
            Path(
                "emdash3_2_abelian_snake_six_term_"
                "inner_kernel_u_zero_foundation.lp"
            ),
            Path("examples/abelian_snake_six_term_inner_zero.lp"),
            Path("emdash3_2_abelian_snake_exact_third_result.lp"),
            Path("emdash3_2_abelian_snake_six_term_exact_result.lp"),
        ]

        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")

        self.assertEqual(status, 0)
        self.assertEqual(run_command.call_count, 2)
        self.assertEqual(
            run_command.call_args_list[1],
            call(["./scripts/check_abelian_snake_six_term.sh"]),
        )
        self.assertEqual(
            [result.evidence for result in results],
            [
                "current",
                "current-isolated-object-chain",
                "current-isolated-object-chain",
                "current-isolated-object-chain",
                "current-isolated-object-chain",
            ],
        )

    @patch("scripts.check_metrics.run_command")
    def test_normalization_and_snake_groups_run_independently_once(self, run_command) -> None:
        run_command.side_effect = [(0, "", 2.0), (0, "", 4.0)]
        files = [
            Path("emdash3_2_short_exact_normalization.lp"),
            Path("emdash3_2_abelian_snake_six_term_exact_result.lp"),
            Path("examples/short_exact_normalization.lp"),
            Path("examples/abelian_snake_six_term_exact_result.lp"),
        ]
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        self.assertEqual(run_command.call_args_list, [
            call(["./scripts/check_short_exact_normalization.sh"]),
            call(["./scripts/check_abelian_snake_six_term.sh"]),
        ])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    @patch("scripts.check_metrics.run_command")
    def test_snake_row_owners_and_reviewers_share_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 8.0)
        files = [
            Path("emdash3_2_chain_pair_map_snake.lp"),
            Path("emdash3_2_short_exact_row_snake.lp"),
            Path("examples/snake_row_source_cycle_iso.lp"),
            Path("examples/short_exact_row_snake_target.lp"),
        ]
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_snake_row_comparisons.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_snake_row_dispatch_matches_the_actual_script_targets(self) -> None:
        script = Path(__file__).resolve().parents[1] / "scripts/check_snake_row_comparisons.sh"
        targets = {
            Path(name) for name in re.findall(
                r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$",
                script.read_text(encoding="utf-8"), re.MULTILINE,
            )
        }
        self.assertEqual(len(targets), 17)
        self.assertEqual(targets, SPECIAL_SNAKE_ROW_CHECK_FILES)

    @patch("scripts.check_metrics.run_command")
    def test_target_cycle_owners_and_reviewers_share_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 12.0)
        files = sorted(SPECIAL_SNAKE_TARGET_CYCLE_CHECK_FILES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_snake_row_target_cycles.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_target_cycle_dispatch_matches_the_actual_script_targets(self) -> None:
        script = Path(__file__).resolve().parents[1] / "scripts/check_snake_row_target_cycles.sh"
        targets = {
            Path(name) for name in re.findall(
                r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$",
                script.read_text(encoding="utf-8"), re.MULTILINE,
            )
        }
        self.assertEqual(len(targets), 9)
        self.assertEqual(targets, SPECIAL_SNAKE_TARGET_CYCLE_CHECK_FILES)

    @patch("scripts.check_metrics.run_command")
    def test_target_cycle_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "target cycle timeout", 90.0)
        files = [Path("emdash3_2_snake_row_target_cycles.lp"), Path("examples/snake_row_target_cycles.lp")]
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_snake_row_target_cycles.sh"])
        self.assertTrue(all(result.returncode == 124 for result in results))

    @patch("scripts.check_metrics.run_command")
    def test_target_homology_owners_and_reviewers_share_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 18.0)
        files = sorted(SPECIAL_SNAKE_TARGET_HOMOLOGY_CHECK_FILES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_snake_row_target_homology.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_target_homology_dispatch_matches_owned_script_targets(self) -> None:
        script = Path(__file__).resolve().parents[1] / "scripts/check_snake_row_target_homology.sh"
        source = script.read_text(encoding="utf-8")
        sections = [re.search(rf"{name}=\((.*?)\n\)", source, re.DOTALL).group(1)
                    for name in ("owners", "reviewers")]
        targets = {Path(name) for section in sections for name in re.findall(
            r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$", section, re.MULTILINE)}
        self.assertEqual(len(targets), 6)
        self.assertEqual(targets, SPECIAL_SNAKE_TARGET_HOMOLOGY_CHECK_FILES)
        self.assertIn("prerequisites=(", source)
        self.assertIn("check_object examples/snake_row_target_cycles.lp", source)

    @patch("scripts.check_metrics.run_command")
    def test_target_homology_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "target homology timeout", 90.0)
        files = sorted(SPECIAL_SNAKE_TARGET_HOMOLOGY_CHECK_FILES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_snake_row_target_homology.sh"])
        self.assertTrue(all(result.returncode == 124 for result in results))

    @patch("scripts.check_metrics.run_command")
    def test_snake_row_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "bounded consumer timeout", 90.0)
        files = [
            Path("emdash3_2_abelian_snake_row_comparisons.lp"),
            Path("examples/short_exact_row_snake.lp"),
        ]
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_snake_row_comparisons.sh"])
        self.assertTrue(all(result.returncode == 124 for result in results))

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
