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
    ISOLATED_CHECK_GROUPS,
    NATIVE_SIX_TERM_GC_CHECK_FILES,
    NATIVE_SIX_TERM_GC_SCRIPT,
    NATIVE_SNAKE_PAIR_CHECK_FILES,
    NATIVE_SNAKE_PAIR_SCRIPT,
    lambdapi_check_command,
    SPECIAL_HOMOLOGY_EXACT_WINDOW_CHECK_FILES,
    SPECIAL_HOMOLOGY_WINDOW_FAMILY_CHECK_FILES,
    SPECIAL_HOMOLOGY_ARROW_TAIL_CHECK_FILES,
    SPECIAL_HOMOLOGY_BOUNDED_PREREQUISITES,
    SPECIAL_HOMOLOGY_BOUNDED_GENERATOR,
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
    def test_current_groups_run_independently_without_reordering_results(self, run_command) -> None:
        first_targets, first_script = ISOLATED_CHECK_GROUPS[-2]
        second_targets, second_script = ISOLATED_CHECK_GROUPS[-1]
        self.assertFalse(first_targets & second_targets)
        first, second = sorted(first_targets), sorted(second_targets)
        files = [first[0], second[0], first[-1], second[-1]]
        run_command.side_effect = [(0, "", 2.0), (0, "", 4.0)]
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        self.assertEqual(run_command.call_args_list, [call([first_script]), call([second_script])])
        self.assertEqual([r.file for r in results], [str(p) for p in files])

    @patch("scripts.check_metrics.run_command")
    def test_current_isolated_groups_run_once_and_keep_failures(self, run_command) -> None:
        for targets, script in ISOLATED_CHECK_GROUPS:
            for code in (0, 124):
                with self.subTest(script=script, exit_code=code):
                    run_command.reset_mock()
                    run_command.return_value = (code, "group result", 3.0)
                    files = sorted(targets)
                    with redirect_stdout(StringIO()):
                        results, status = run_checks(files, "90s")
                    run_command.assert_called_once_with([script])
                    self.assertEqual([r.file for r in results], [str(p) for p in files])
                    self.assertTrue(all(r.returncode == code for r in results))
                    self.assertEqual(status == 0, code == 0)
                    if code == 0:
                        self.assertTrue(all(r.evidence == "current-isolated-object-chain" for r in results))

    def test_current_native_targets_use_their_guarded_per_file_commands(self) -> None:
        for targets, script in (
            (NATIVE_SIX_TERM_GC_CHECK_FILES, NATIVE_SIX_TERM_GC_SCRIPT),
            (NATIVE_SNAKE_PAIR_CHECK_FILES, NATIVE_SNAKE_PAIR_SCRIPT),
        ):
            for target in sorted(targets):
                with self.subTest(target=target):
                    self.assertEqual(lambdapi_check_command(target), [f"./{script}", str(target)])
                    self.assertTrue((Path(__file__).resolve().parents[1] / target).is_file())


    @patch("scripts.check_metrics.run_command")
    def test_exact_window_owners_and_reviewer_share_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 24.0)
        files = sorted(SPECIAL_HOMOLOGY_EXACT_WINDOW_CHECK_FILES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_exact_window.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_exact_window_dispatch_matches_owned_script_targets(self) -> None:
        script_dir = Path(__file__).resolve().parents[1] / "scripts"
        source = (script_dir / "check_homology_exact_window.sh").read_text(encoding="utf-8")
        sections = [re.search(rf"{name}=\((.*?)\n\)", source, re.DOTALL).group(1)
                    for name in ("owners", "reviewers")]
        targets = {Path(name) for section in sections for name in re.findall(
            r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$", section, re.MULTILINE)}
        self.assertEqual(len(targets), 3)
        self.assertEqual(targets, SPECIAL_HOMOLOGY_EXACT_WINDOW_CHECK_FILES)
        for name in ("first", "second", "third"):
            self.assertIn(f"emdash3_2_homology_{name}_exactness.lp", source)
        for name in ("check.sh", "check_examples.sh"):
            self.assertIn("./scripts/check_homology_exact_window.sh",
                          (script_dir / name).read_text(encoding="utf-8"))

    @patch("scripts.check_metrics.run_command")
    def test_exact_window_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "exact window timeout", 90.0)
        files = sorted(SPECIAL_HOMOLOGY_EXACT_WINDOW_CHECK_FILES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_exact_window.sh"])
        self.assertTrue(all(result.returncode == 124 for result in results))


    @patch("scripts.check_metrics.run_command")
    def test_window_family_targets_share_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 18.0)
        files = sorted(SPECIAL_HOMOLOGY_WINDOW_FAMILY_CHECK_FILES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_window_families.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_window_family_dispatch_matches_script_targets(self) -> None:
        script_dir = Path(__file__).resolve().parents[1] / "scripts"
        source = (script_dir / "check_homology_window_families.sh").read_text(encoding="utf-8")
        sections = [re.search(rf"{name}=\((.*?)\n\)", source, re.DOTALL).group(1)
                    for name in ("owners", "reviewers")]
        targets = {Path(name) for section in sections for name in re.findall(
            r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$", section, re.MULTILINE)}
        self.assertEqual(len(targets), 9)
        self.assertEqual(targets - {Path("examples/homology_record_connecting_whole.lp")},
                         SPECIAL_HOMOLOGY_WINDOW_FAMILY_CHECK_FILES)
        for name in ("check.sh", "check_examples.sh"):
            self.assertIn("./scripts/check_homology_window_families.sh",
                          (script_dir / name).read_text(encoding="utf-8"))

    @patch("scripts.check_metrics.run_command")
    def test_window_family_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "window family timeout", 90.0)
        with redirect_stdout(StringIO()):
            results, status = run_checks(sorted(SPECIAL_HOMOLOGY_WINDOW_FAMILY_CHECK_FILES), "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_window_families.sh"])
        self.assertTrue(all(result.returncode == 124 for result in results))

    @patch("scripts.check_metrics.run_command")
    def test_arrow_tail_targets_share_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 20.0)
        files = sorted(SPECIAL_HOMOLOGY_ARROW_TAIL_CHECK_FILES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_arrow_tails.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_arrow_tail_dispatch_matches_script_targets(self) -> None:
        script_dir = Path(__file__).resolve().parents[1] / "scripts"
        source = (script_dir / "check_homology_arrow_tails.sh").read_text(encoding="utf-8")
        sections = [re.search(rf"{name}=\((.*?)\n\)", source, re.DOTALL).group(1)
                    for name in ("owners", "reviewers")]
        targets = {Path(name) for section in sections for name in re.findall(
            r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$", section, re.MULTILINE)}
        self.assertEqual(targets - {
            Path("emdash3_2_homology_exact_window.lp"),
            Path("emdash3_2_homology_exact_window_result.lp"),
        }, SPECIAL_HOMOLOGY_ARROW_TAIL_CHECK_FILES)
        for name in ("check.sh", "check_examples.sh"):
            self.assertIn("./scripts/check_homology_arrow_tails.sh",
                          (script_dir / name).read_text(encoding="utf-8"))

    @patch("scripts.check_metrics.run_command")
    def test_arrow_tail_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "arrow-tail timeout", 90.0)
        with redirect_stdout(StringIO()):
            results, status = run_checks(sorted(SPECIAL_HOMOLOGY_ARROW_TAIL_CHECK_FILES), "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_arrow_tails.sh"])
        self.assertTrue(all(result.returncode == 124 for result in results))

    @patch("scripts.check_metrics.run_command")
    def test_bounded_prerequisites_share_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 22.0)
        files = sorted(SPECIAL_HOMOLOGY_BOUNDED_PREREQUISITES)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_bounded_prerequisites.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_bounded_prerequisite_dispatch_matches_script_targets(self) -> None:
        script_dir = Path(__file__).resolve().parents[1] / "scripts"
        source = (script_dir / "check_homology_bounded_prerequisites.sh").read_text(encoding="utf-8")
        sections = [re.search(rf"{name}=\((.*?)\n\)", source, re.DOTALL).group(1)
                    for name in ("owners", "reviewers")]
        targets = {Path(name) for section in sections for name in re.findall(
            r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$", section, re.MULTILINE)}
        reused = {
            Path("emdash3_2_homology_exact_window.lp"), Path("emdash3_2_homology_exact_window_result.lp"),
            Path("emdash3_2_finite_arrow_tails.lp"), Path("emdash3_2_finite_arrow_tail_append.lp"),
            Path("emdash3_2_computational_exact_arrow_tails.lp"), Path("examples/homology_adjacent_window_tails.lp"),
        }
        self.assertEqual(targets - reused, SPECIAL_HOMOLOGY_BOUNDED_PREREQUISITES)
        for name in ("check.sh", "check_examples.sh"):
            self.assertIn("./scripts/check_homology_bounded_prerequisites.sh",
                          (script_dir / name).read_text(encoding="utf-8"))

    @patch("scripts.check_metrics.run_command")
    def test_bounded_prerequisite_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "bounded prerequisite timeout", 90.0)
        with redirect_stdout(StringIO()):
            results, status = run_checks(sorted(SPECIAL_HOMOLOGY_BOUNDED_PREREQUISITES), "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_bounded_prerequisites.sh"])
        self.assertTrue(all(result.returncode == 124 for result in results))

    @patch("scripts.check_metrics.run_command")
    def test_bounded_generator_shares_one_fresh_chain(self, run_command) -> None:
        run_command.return_value = (0, "", 22.0)
        files = sorted(SPECIAL_HOMOLOGY_BOUNDED_GENERATOR)
        with redirect_stdout(StringIO()):
            results, status = run_checks(files, "90s")
        self.assertEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_bounded_generator.sh"])
        self.assertEqual([result.file for result in results], [str(path) for path in files])
        self.assertTrue(all(result.evidence == "current-isolated-object-chain" for result in results))

    def test_bounded_generator_dispatch_matches_script_targets(self) -> None:
        script_dir = Path(__file__).resolve().parents[1] / "scripts"
        source = (script_dir / "check_homology_bounded_generator.sh").read_text(encoding="utf-8")
        sections = [re.search(rf"{name}=\((.*?)\n\)", source, re.DOTALL).group(1)
                    for name in ("owners", "reviewers")]
        targets = {Path(name) for section in sections for name in re.findall(
            r"^\s+((?:examples/)?[a-z][a-z0-9_]*\.lp)$", section, re.MULTILINE)}
        reused = SPECIAL_HOMOLOGY_BOUNDED_PREREQUISITES | SPECIAL_HOMOLOGY_ARROW_TAIL_CHECK_FILES | {
            Path("emdash3_2_homology_exact_window.lp"), Path("emdash3_2_homology_exact_window_result.lp"),
        }
        self.assertEqual(targets - reused, SPECIAL_HOMOLOGY_BOUNDED_GENERATOR)
        for name in ("check.sh", "check_examples.sh"):
            self.assertIn("./scripts/check_homology_bounded_generator.sh",
                          (script_dir / name).read_text(encoding="utf-8"))

    @patch("scripts.check_metrics.run_command")
    def test_bounded_generator_failure_is_not_reported_as_checked(self, run_command) -> None:
        run_command.return_value = (124, "bounded generator timeout", 90.0)
        with redirect_stdout(StringIO()):
            results, status = run_checks(sorted(SPECIAL_HOMOLOGY_BOUNDED_GENERATOR), "90s")
        self.assertNotEqual(status, 0)
        run_command.assert_called_once_with(["./scripts/check_homology_bounded_generator.sh"])
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
