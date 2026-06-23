from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = REPO_ROOT / "scripts" / "infinity_codex.py"
HOOKS = REPO_ROOT / ".codex" / "hooks.json"


class InfinityCodexTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.archive = Path(self.temporary.name) / "archive"

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_cli(
        self,
        *arguments: str,
        stdin: bytes | None = None,
        now: str = "2026-06-23T12:34:56Z",
        check: bool = True,
    ) -> subprocess.CompletedProcess[bytes]:
        environment = os.environ.copy()
        environment["INFINITY_CODEX_NOW"] = now
        result = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--archive-root",
                str(self.archive),
                *arguments,
            ],
            cwd=REPO_ROOT,
            env=environment,
            input=stdin,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if check and result.returncode != 0:
            self.fail(
                f"command failed ({result.returncode}): {result.stderr.decode()}"
            )
        return result

    def stop_payload(
        self,
        message: str | None,
        *,
        session_id: str = "019ef43a-0c30-78c2-8f2e-7be96cb03a12",
        turn_id: str = "turn-0001",
    ) -> dict[str, object]:
        return {
            "session_id": session_id,
            "turn_id": turn_id,
            "transcript_path": "/unstable/transcript.jsonl",
            "cwd": str(REPO_ROOT),
            "hook_event_name": "Stop",
            "model": "gpt-test",
            "permission_mode": "default",
            "stop_hook_active": False,
            "last_assistant_message": message,
        }

    def run_hook(
        self, payload: dict[str, object], *, now: str = "2026-06-23T12:34:56Z"
    ) -> dict[str, object]:
        result = self.run_cli(
            "hook",
            stdin=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
            now=now,
        )
        return json.loads(result.stdout)

    def one_response(self) -> Path:
        responses = list(self.archive.glob("sessions/*/responses/*.md"))
        self.assertEqual(len(responses), 1)
        return responses[0]

    def one_metadata(self) -> Path:
        metadata = list(self.archive.glob("sessions/*/metadata/*.json"))
        self.assertEqual(len(metadata), 1)
        return metadata[0]

    def test_stop_preserves_exact_unicode_bytes_without_newline(self) -> None:
        message = "First line\nβ → ω\nfinal byte"
        result = self.run_hook(self.stop_payload(message))
        self.assertEqual(result, {"continue": True})

        response = self.one_response()
        expected = message.encode("utf-8")
        self.assertEqual(response.read_bytes(), expected)
        self.assertFalse(response.read_bytes().endswith(b"\n"))

        metadata = json.loads(self.one_metadata().read_text(encoding="utf-8"))
        self.assertEqual(metadata["byte_count"], len(expected))
        self.assertEqual(metadata["sha256"], hashlib.sha256(expected).hexdigest())
        self.assertEqual(
            metadata["logical_id"],
            "infinity-codex:019ef43a-0c30-78c2-8f2e-7be96cb03a12:turn-0001",
        )

    def test_null_message_creates_no_archive(self) -> None:
        result = self.run_hook(self.stop_payload(None))
        self.assertEqual(result, {"continue": True})
        self.assertFalse(self.archive.exists())

    def test_duplicate_turn_is_idempotent(self) -> None:
        payload = self.stop_payload("same response")
        self.run_hook(payload)
        first_path = self.one_response()
        self.run_hook(payload, now="2026-06-24T01:02:03Z")
        self.assertEqual(list(self.archive.glob("sessions/*/responses/*.md")), [first_path])
        self.assertEqual(len(list(self.archive.glob("sessions/*/metadata/*.json"))), 1)

    def test_conflicting_duplicate_is_preserved_and_diagnosed(self) -> None:
        payload = self.stop_payload("original")
        self.run_hook(payload)
        response = self.one_response()

        payload["last_assistant_message"] = "replacement"
        result = self.run_hook(payload, now="2026-06-24T01:02:03Z")
        self.assertIn("systemMessage", result)
        self.assertIn("archive conflict", str(result["systemMessage"]).lower())
        self.assertEqual(response.read_bytes(), b"original")
        self.assertEqual(len(list(self.archive.glob("diagnostics/*.json"))), 1)

    def test_resumed_session_reuses_directory_and_increments_sequence(self) -> None:
        session_id = "session-resumed-across-days"
        self.run_hook(
            self.stop_payload("first", session_id=session_id, turn_id="turn-a"),
            now="2026-06-23T23:59:59Z",
        )
        self.run_hook(
            self.stop_payload("second", session_id=session_id, turn_id="turn-b"),
            now="2026-06-24T00:00:01Z",
        )

        sessions = list(self.archive.glob("sessions/*"))
        self.assertEqual(len(sessions), 1)
        responses = sorted((sessions[0] / "responses").glob("*.md"))
        self.assertEqual([path.name[:4] for path in responses], ["0001", "0002"])
        self.assertTrue(sessions[0].name.startswith("2026-06-23_"))

    def test_logical_id_resolution_show_and_latest(self) -> None:
        message = "verbatim output"
        self.run_hook(self.stop_payload(message))
        logical = self.run_cli("latest-id").stdout.decode().strip()
        resolved = Path(self.run_cli("resolve", logical).stdout.decode().strip())
        self.assertEqual(resolved, self.one_response())
        self.assertEqual(self.run_cli("show", logical).stdout, message.encode())

    def test_session_start_injects_only_recovery_pointers(self) -> None:
        marker = "DO-NOT-INJECT-ARCHIVED-CONTENT"
        payload = self.stop_payload(marker)
        self.run_hook(payload)
        start_payload = {
            "session_id": payload["session_id"],
            "transcript_path": "/unstable/transcript.jsonl",
            "cwd": str(REPO_ROOT),
            "hook_event_name": "SessionStart",
            "model": "gpt-test",
            "permission_mode": "default",
            "source": "compact",
        }
        result = self.run_hook(start_payload)
        context = result["hookSpecificOutput"]["additionalContext"]
        self.assertIn("Local archive index:", context)
        self.assertIn("Latest archived final:", context)
        self.assertIn("Authority order:", context)
        self.assertNotIn(marker, context)

    def test_archive_permissions_and_verify(self) -> None:
        self.run_hook(self.stop_payload("private"))
        for path in [self.archive, *self.archive.rglob("*")]:
            expected = 0o700 if path.is_dir() else 0o600
            self.assertEqual(stat.S_IMODE(path.stat().st_mode), expected, path)
        verify = self.run_cli("verify")
        self.assertIn(b"archive verified", verify.stdout)

    def test_verify_rejects_corrupt_metadata(self) -> None:
        self.run_hook(self.stop_payload("valid"))
        self.one_metadata().write_text("{not json", encoding="utf-8")
        verify = self.run_cli("verify", check=False)
        self.assertEqual(verify.returncode, 1)
        self.assertIn(b"Expecting property name", verify.stderr)

    def test_prune_is_dry_run_by_default_and_apply_is_explicit(self) -> None:
        self.run_hook(
            self.stop_payload("old"),
            now="2026-06-01T00:00:00Z",
        )
        preview = self.run_cli("prune", "--before", "2026-06-02", "--dry-run")
        self.assertIn(b"would delete", preview.stdout)
        self.assertTrue(self.one_response().exists())

        applied = self.run_cli("prune", "--before", "2026-06-02", "--apply")
        self.assertIn(b"mode=apply", applied.stdout)
        self.assertEqual(list(self.archive.glob("sessions/*/responses/*.md")), [])

    def test_annotate_plan_uses_logical_ids_and_preserves_mode(self) -> None:
        self.run_hook(self.stop_payload("decision"))
        logical = self.run_cli("latest-id").stdout.decode().strip()
        fd, name = tempfile.mkstemp(
            prefix="TMP_INFINITY_CODEX_PLAN_",
            suffix=".md",
            dir=REPO_ROOT / "reports",
        )
        report = Path(name)
        try:
            os.close(fd)
            report.write_text(
                "# Temporary Plan\n\n"
                "Infinity-Codex-Origin: pending\n"
                "Infinity-Codex-Decision-Responses: none\n",
                encoding="utf-8",
            )
            os.chmod(report, 0o644)
            self.run_cli("annotate-plan", "--origin", logical, str(report))
            self.run_cli("annotate-plan", "--decision", logical, str(report))
            text = report.read_text(encoding="utf-8")
            self.assertIn(f"Infinity-Codex-Origin: {logical}", text)
            self.assertIn(f"Infinity-Codex-Decision-Responses: {logical}", text)
            self.assertEqual(stat.S_IMODE(report.stat().st_mode), 0o644)
        finally:
            report.unlink(missing_ok=True)

    def test_hook_configuration_has_only_stop_and_recovery_events(self) -> None:
        configuration = json.loads(HOOKS.read_text(encoding="utf-8"))
        hooks = configuration["hooks"]
        self.assertEqual(set(hooks), {"Stop", "SessionStart"})
        self.assertEqual(hooks["SessionStart"][0]["matcher"], "resume|compact")
        for event in hooks.values():
            command = event[0]["hooks"][0]["command"]
            self.assertIn("scripts/infinity_codex.py", command)
            self.assertTrue(command.endswith(" hook"))


if __name__ == "__main__":
    unittest.main()
