from __future__ import annotations

import importlib.util
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

spec = importlib.util.spec_from_file_location("validation_artifacts", Path(__file__).resolve().parents[2] / ".github/scripts/validation_artifacts.py")
artifacts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(artifacts)


class ValidationArtifactTests(unittest.TestCase):
    def setUp(self):
        self.run = {"id": 12, "run_attempt": 2, "status": "completed", "conclusion": "success",
                    "event": "push", "head_branch": "main", "head_repository": {"full_name": "owner/repo"},
                    "path": ".github/workflows/validate.yml", "head_sha": "a" * 40}

    def test_base_uses_prior_qualified_run_not_the_previous_push(self):
        failed = {**self.run, "id": 13, "conclusion": "failure", "head_sha": "b" * 40}
        cancelled = {**self.run, "id": 14, "conclusion": "cancelled", "head_sha": "c" * 40}
        self.assertEqual(artifacts.qualified_base([self.run, failed, cancelled], "owner/repo", "d" * 40), "a" * 40)
        self.assertIsNone(artifacts.qualified_base([failed, cancelled], "owner/repo", "d" * 40))

    def test_publication_rejects_forks_prs_failure_and_other_workflows(self):
        for change in ({"event": "pull_request"}, {"conclusion": "failure"}, {"status": "in_progress"},
                       {"head_repository": {"full_name": "fork/repo"}}, {"path": ".github/workflows/other.yml"},
                       {"head_branch": "feature"}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                artifacts.select_artifact({**self.run, **change}, [], "owner/repo")

    def test_artifact_selection_is_exact_to_successful_attempt(self):
        result = artifacts.select_artifact(self.run, [{"name": "reviewer-dist-1", "expired": False}], "owner/repo")
        self.assertFalse(result["deploy"])
        result = artifacts.select_artifact(self.run, [{"name": "reviewer-dist-2", "expired": False}], "owner/repo")
        self.assertTrue(result["deploy"])
        with self.assertRaises(ValueError):
            artifacts.select_artifact(self.run, [], "owner/repo", manual=True)

    def test_manual_validation_requires_manual_publication(self):
        run = {**self.run, "event": "workflow_dispatch"}
        with self.assertRaises(ValueError):
            artifacts.select_artifact(run, [], "owner/repo")
        self.assertTrue(artifacts.select_artifact(run, [{"name": "reviewer-dist-2"}], "owner/repo", manual=True)["deploy"])

    def test_bundle_tampering_missing_extra_and_wrong_identity_are_rejected(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "index.html").write_text("checked bundle")
            artifacts.write_manifest(root, "a" * 40, "12", "2")
            artifacts.verify_manifest(root, "a" * 40, "12", "2")
            with self.assertRaises(ValueError):
                artifacts.verify_manifest(root, "b" * 40, "12", "2")
            (root / "extra.js").write_text("extra")
            with self.assertRaises(ValueError):
                artifacts.verify_manifest(root, "a" * 40, "12", "2")
            (root / "extra.js").unlink()
            (root / "index.html").write_text("changed bundle")
            with self.assertRaises(ValueError):
                artifacts.verify_manifest(root, "a" * 40, "12", "2")


if __name__ == "__main__":
    unittest.main()
