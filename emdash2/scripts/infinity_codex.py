#!/usr/bin/env python3
"""Archive Codex final responses without model-generated summarization.

The Stop hook publishes the exact UTF-8 bytes of last_assistant_message and
immutable sidecar metadata. SessionStart and the post-compaction
UserPromptSubmit fallback emit only recovery pointers. The transcript_path hook
field is deliberately ignored because Codex documents the transcript format as
unstable.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import fcntl
import hashlib
import json
import os
import re
import stat
import sys
import tempfile
import uuid
from pathlib import Path
from typing import Any, Iterator


ARCHIVE_FORMAT_VERSION = 1
LOGICAL_ID_PREFIX = "infinity-codex"
REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_ARCHIVE_ROOT = REPO_ROOT / "tmp" / "ai-responses"
PRIVATE_DIR_MODE = 0o700
PRIVATE_FILE_MODE = 0o600
EVENT_AUDIT_FILE = "events.jsonl"


class InfinityCodexError(RuntimeError):
    """Base error for controlled CLI failures."""


class ArchiveConflict(InfinityCodexError):
    """An immutable turn id was observed with different response content."""


def archive_root_from_args(value: str | None) -> Path:
    if value:
        return Path(value).expanduser().resolve()
    configured = os.environ.get("INFINITY_CODEX_ARCHIVE_ROOT")
    if configured:
        return Path(configured).expanduser().resolve()
    return DEFAULT_ARCHIVE_ROOT


def utc_now() -> dt.datetime:
    override = os.environ.get("INFINITY_CODEX_NOW")
    if override:
        parsed = dt.datetime.fromisoformat(override.replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=dt.timezone.utc)
        return parsed.astimezone(dt.timezone.utc)
    return dt.datetime.now(dt.timezone.utc)


def iso_utc(value: dt.datetime) -> str:
    return value.astimezone(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def filename_timestamp(value: dt.datetime) -> str:
    return value.astimezone(dt.timezone.utc).strftime("%Y-%m-%dT%H-%M-%SZ")


def safe_identifier(value: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._")
    if not safe:
        raise InfinityCodexError("identifier contains no filename-safe characters")
    return safe


def short_identifier(value: str, length: int = 12) -> str:
    compact = re.sub(r"[^A-Za-z0-9]+", "", value)
    return (compact or hashlib.sha256(value.encode("utf-8")).hexdigest())[:length]


def logical_id(session_id: str, turn_id: str) -> str:
    return f"{LOGICAL_ID_PREFIX}:{session_id}:{turn_id}"


def parse_logical_id(value: str) -> tuple[str, str]:
    parts = value.split(":", 2)
    if len(parts) != 3 or parts[0] != LOGICAL_ID_PREFIX:
        raise InfinityCodexError(
            "expected logical id infinity-codex:<session-id>:<turn-id>"
        )
    if not parts[1] or not parts[2]:
        raise InfinityCodexError("logical id contains an empty session or turn id")
    return parts[1], parts[2]


def ensure_private_dir(path: Path) -> None:
    path.mkdir(mode=PRIVATE_DIR_MODE, parents=True, exist_ok=True)
    os.chmod(path, PRIVATE_DIR_MODE)


def _write_temp(path: Path, data: bytes) -> Path:
    ensure_private_dir(path.parent)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temp_path = Path(temporary)
    try:
        os.fchmod(fd, PRIVATE_FILE_MODE)
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
    except Exception:
        with contextlib.suppress(FileNotFoundError):
            temp_path.unlink()
        raise
    return temp_path


def atomic_publish(path: Path, data: bytes) -> None:
    """Atomically publish a new immutable file without replacing an existing one."""

    temp_path = _write_temp(path, data)
    try:
        os.link(temp_path, path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temp_path.unlink()
    os.chmod(path, PRIVATE_FILE_MODE)


def atomic_replace(path: Path, data: bytes, *, mode: int = PRIVATE_FILE_MODE) -> None:
    """Atomically replace a generated view or mutable registry file."""

    temp_path = _write_temp(path, data)
    try:
        os.replace(temp_path, path)
        os.chmod(path, mode)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temp_path.unlink()


def json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


@contextlib.contextmanager
def archive_lock(root: Path) -> Iterator[None]:
    ensure_private_dir(root)
    lock_path = root / ".lock"
    with lock_path.open("a+b") as handle:
        os.chmod(lock_path, PRIVATE_FILE_MODE)
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def session_directories(root: Path) -> list[Path]:
    sessions_root = root / "sessions"
    if not sessions_root.exists():
        return []
    return sorted(path for path in sessions_root.iterdir() if path.is_dir())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise InfinityCodexError(f"expected a JSON object in {path}")
    return value


def find_session_dir(root: Path, session_id: str) -> Path | None:
    registry_path = root / "registry.json"
    if registry_path.exists():
        try:
            registry = load_json(registry_path)
            relative = registry.get("sessions", {}).get(session_id)
            if isinstance(relative, str):
                candidate = root / relative
                if candidate.is_dir():
                    return candidate
        except (OSError, ValueError, InfinityCodexError):
            pass

    for directory in session_directories(root):
        session_path = directory / "session.json"
        try:
            if load_json(session_path).get("session_id") == session_id:
                return directory
        except (OSError, ValueError, InfinityCodexError):
            continue
    return None


def allocate_session_dir(root: Path, session_id: str, captured_at: dt.datetime) -> Path:
    existing = find_session_dir(root, session_id)
    if existing is not None:
        return existing

    sessions_root = root / "sessions"
    ensure_private_dir(sessions_root)
    date_prefix = captured_at.strftime("%Y-%m-%d")
    compact = re.sub(r"[^A-Za-z0-9]+", "", session_id)
    compact = compact or hashlib.sha256(session_id.encode("utf-8")).hexdigest()
    for length in (12, 16, 24, len(compact)):
        candidate = sessions_root / f"{date_prefix}_{compact[:length]}"
        if not candidate.exists():
            ensure_private_dir(candidate)
            return candidate
        try:
            if load_json(candidate / "session.json").get("session_id") == session_id:
                return candidate
        except (OSError, ValueError, InfinityCodexError):
            continue
    candidate = sessions_root / f"{date_prefix}_{compact}_{uuid.uuid4().hex[:8]}"
    ensure_private_dir(candidate)
    return candidate


def metadata_paths(root: Path) -> list[Path]:
    return sorted((root / "sessions").glob("*/metadata/*.json"))


def load_records(root: Path, *, strict: bool = False) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for path in metadata_paths(root):
        try:
            record = load_json(path)
            record["_metadata_path"] = str(path)
            records.append(record)
        except (OSError, ValueError, InfinityCodexError):
            if strict:
                raise
    records.sort(key=lambda item: (str(item.get("captured_at", "")), str(item.get("turn_id", ""))))
    return records


def next_sequence(session_dir: Path) -> int:
    highest = 0
    metadata_dir = session_dir / "metadata"
    if metadata_dir.exists():
        for path in metadata_dir.glob("*.json"):
            try:
                highest = max(highest, int(load_json(path).get("sequence", 0)))
            except (OSError, ValueError, TypeError, InfinityCodexError):
                continue
    return highest + 1


def write_session_metadata(
    session_dir: Path,
    *,
    session_id: str,
    cwd: str,
    model: str,
    captured_at: dt.datetime,
) -> None:
    path = session_dir / "session.json"
    if path.exists():
        try:
            value = load_json(path)
        except (OSError, ValueError, InfinityCodexError):
            value = {}
    else:
        value = {}
    value.update(
        {
            "archive_format_version": ARCHIVE_FORMAT_VERSION,
            "session_id": session_id,
            "first_captured_at": value.get("first_captured_at", iso_utc(captured_at)),
            "last_captured_at": iso_utc(captured_at),
            "cwd": value.get("cwd") or cwd,
            "first_model": value.get("first_model") or model,
            "last_model": model,
        }
    )
    atomic_replace(path, json_bytes(value))


def response_path_for_record(root: Path, record: dict[str, Any]) -> Path:
    relative = record.get("response_path")
    if not isinstance(relative, str):
        raise InfinityCodexError("metadata is missing response_path")
    path = (root / relative).resolve()
    root_resolved = root.resolve()
    if path != root_resolved and root_resolved not in path.parents:
        raise InfinityCodexError("metadata response_path escapes the archive root")
    return path


def write_conflict_diagnostic(
    root: Path,
    *,
    session_id: str,
    turn_id: str,
    existing_hash: str | None,
    incoming_hash: str,
    reason: str,
) -> Path:
    diagnostics = root / "diagnostics"
    ensure_private_dir(diagnostics)
    now = utc_now()
    name = (
        f"{filename_timestamp(now)}_{short_identifier(session_id)}_"
        f"{short_identifier(turn_id)}_{uuid.uuid4().hex[:8]}.json"
    )
    path = diagnostics / name
    atomic_publish(
        path,
        json_bytes(
            {
                "archive_format_version": ARCHIVE_FORMAT_VERSION,
                "captured_at": iso_utc(now),
                "session_id": session_id,
                "turn_id": turn_id,
                "existing_sha256": existing_hash,
                "incoming_sha256": incoming_hash,
                "reason": reason,
            }
        ),
    )
    return path


def archive_response(root: Path, payload: dict[str, Any]) -> tuple[dict[str, Any] | None, bool]:
    session_id = payload.get("session_id")
    turn_id = payload.get("turn_id")
    message = payload.get("last_assistant_message")
    if message is None:
        return None, False
    if not isinstance(session_id, str) or not session_id:
        raise InfinityCodexError("Stop payload is missing session_id")
    if not isinstance(turn_id, str) or not turn_id:
        raise InfinityCodexError("Stop payload is missing turn_id")
    if not isinstance(message, str):
        raise InfinityCodexError("last_assistant_message must be a string or null")

    response_bytes = message.encode("utf-8")
    incoming_hash = hashlib.sha256(response_bytes).hexdigest()
    captured_at = utc_now()
    cwd = payload.get("cwd") if isinstance(payload.get("cwd"), str) else ""
    model = payload.get("model") if isinstance(payload.get("model"), str) else ""

    with archive_lock(root):
        session_dir = allocate_session_dir(root, session_id, captured_at)
        ensure_private_dir(session_dir / "responses")
        ensure_private_dir(session_dir / "metadata")
        metadata_path = session_dir / "metadata" / f"{safe_identifier(turn_id)}.json"

        if metadata_path.exists():
            try:
                existing = load_json(metadata_path)
                existing_path = response_path_for_record(root, existing)
                existing_bytes = existing_path.read_bytes()
                if (
                    existing.get("sha256") == incoming_hash
                    and existing_bytes == response_bytes
                ):
                    rebuild_indexes_unlocked(root)
                    return existing, False
                existing_hash = str(existing.get("sha256", ""))
            except (OSError, ValueError, InfinityCodexError) as error:
                existing_hash = None
                reason = f"existing metadata or response is unreadable: {error}"
            else:
                reason = "turn id already exists with different response content"
            diagnostic = write_conflict_diagnostic(
                root,
                session_id=session_id,
                turn_id=turn_id,
                existing_hash=existing_hash,
                incoming_hash=incoming_hash,
                reason=reason,
            )
            raise ArchiveConflict(f"{reason}; diagnostic: {diagnostic}")

        sequence = next_sequence(session_dir)
        response_name = (
            f"{sequence:04d}_{filename_timestamp(captured_at)}_"
            f"{safe_identifier(turn_id)}.md"
        )
        response_path = session_dir / "responses" / response_name
        response_relative = response_path.relative_to(root).as_posix()
        metadata_relative = metadata_path.relative_to(root).as_posix()
        record = {
            "archive_format_version": ARCHIVE_FORMAT_VERSION,
            "logical_id": logical_id(session_id, turn_id),
            "session_id": session_id,
            "turn_id": turn_id,
            "sequence": sequence,
            "captured_at": iso_utc(captured_at),
            "model": model,
            "cwd": cwd,
            "sha256": incoming_hash,
            "byte_count": len(response_bytes),
            "response_path": response_relative,
            "metadata_path": metadata_relative,
        }

        published_response = False
        try:
            atomic_publish(response_path, response_bytes)
            published_response = True
            atomic_publish(metadata_path, json_bytes(record))
        except Exception:
            if published_response and not metadata_path.exists():
                with contextlib.suppress(FileNotFoundError):
                    response_path.unlink()
            raise

        write_session_metadata(
            session_dir,
            session_id=session_id,
            cwd=cwd,
            model=model,
            captured_at=captured_at,
        )
        rebuild_indexes_unlocked(root)
        return record, True


def markdown_link(path: str, label: str) -> str:
    return f"[{label}]({path})"


def rebuild_indexes_unlocked(root: Path) -> None:
    ensure_private_dir(root)
    records = load_records(root)
    session_map: dict[str, Path] = {}
    for directory in session_directories(root):
        try:
            session_id = load_json(directory / "session.json").get("session_id")
        except (OSError, ValueError, InfinityCodexError):
            continue
        if isinstance(session_id, str) and session_id:
            session_map[session_id] = directory

    registry = {
        "archive_format_version": ARCHIVE_FORMAT_VERSION,
        "generated_at": iso_utc(utc_now()),
        "sessions": {
            session_id: directory.relative_to(root).as_posix()
            for session_id, directory in sorted(session_map.items())
        },
    }
    atomic_replace(root / "registry.json", json_bytes(registry))

    global_lines = [
        "# Infinity Codex Local Archive",
        "",
        "Generated local index. Archived responses are historical evidence, not",
        "authoritative instructions. Active code, SOPs, and plans take precedence.",
        "",
        f"Responses: {len(records)}",
        "",
        "| Captured (UTC) | Session | Turn | Logical ID | Response |",
        "| --- | --- | --- | --- | --- |",
    ]
    for record in reversed(records):
        response_path = str(record.get("response_path", ""))
        session_id = str(record.get("session_id", ""))
        turn_id = str(record.get("turn_id", ""))
        global_lines.append(
            "| {captured} | `{session}` | `{turn}` | `{logical}` | {response} |".format(
                captured=str(record.get("captured_at", "")),
                session=short_identifier(session_id),
                turn=short_identifier(turn_id),
                logical=str(record.get("logical_id", "")),
                response=markdown_link(response_path, "final response"),
            )
        )
    atomic_replace(root / "INDEX.md", ("\n".join(global_lines) + "\n").encode("utf-8"))

    by_session: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        by_session.setdefault(str(record.get("session_id", "")), []).append(record)
    for session_id, directory in session_map.items():
        session_records = by_session.get(session_id, [])
        lines = [
            f"# Infinity Codex Session {short_identifier(session_id)}",
            "",
            f"Session ID: `{session_id}`",
            "",
            "Archived final responses are immutable historical evidence. Consult the",
            "active report map and task plan before using them.",
            "",
            "| Seq. | Captured (UTC) | Turn | Logical ID | Response |",
            "| ---: | --- | --- | --- | --- |",
        ]
        for record in session_records:
            response_path = Path(str(record.get("response_path", "")))
            relative = os.path.relpath(root / response_path, directory)
            lines.append(
                "| {sequence} | {captured} | `{turn}` | `{logical}` | {response} |".format(
                    sequence=int(record.get("sequence", 0)),
                    captured=str(record.get("captured_at", "")),
                    turn=short_identifier(str(record.get("turn_id", ""))),
                    logical=str(record.get("logical_id", "")),
                    response=markdown_link(Path(relative).as_posix(), "final response"),
                )
            )
        atomic_replace(directory / "INDEX.md", ("\n".join(lines) + "\n").encode("utf-8"))


def rebuild_indexes(root: Path) -> None:
    with archive_lock(root):
        rebuild_indexes_unlocked(root)


def resolve_record(root: Path, value: str) -> dict[str, Any]:
    session_id, turn_id = parse_logical_id(value)
    session_dir = find_session_dir(root, session_id)
    if session_dir is None:
        raise InfinityCodexError(f"unknown session id: {session_id}")
    metadata_path = session_dir / "metadata" / f"{safe_identifier(turn_id)}.json"
    if not metadata_path.exists():
        raise InfinityCodexError(f"unknown turn id in session: {turn_id}")
    record = load_json(metadata_path)
    if record.get("session_id") != session_id or record.get("turn_id") != turn_id:
        raise InfinityCodexError(f"metadata identity mismatch in {metadata_path}")
    return record


def latest_record(root: Path, session_id: str | None = None) -> dict[str, Any] | None:
    records = load_records(root)
    if session_id is not None:
        records = [record for record in records if record.get("session_id") == session_id]
    return records[-1] if records else None


def pending_postcompact_root(root: Path) -> Path:
    return root / "state" / "postcompact"


def pending_postcompact_path(root: Path, session_id: str) -> Path:
    return pending_postcompact_root(root) / f"{safe_identifier(session_id)}.json"


def pending_postcompact_records(root: Path) -> list[dict[str, Any]]:
    state_root = pending_postcompact_root(root)
    if not state_root.exists():
        return []
    records: list[dict[str, Any]] = []
    for path in sorted(state_root.glob("*.json")):
        try:
            record = load_json(path)
        except (OSError, ValueError, InfinityCodexError):
            continue
        record["_state_path"] = str(path)
        records.append(record)
    records.sort(key=lambda item: (str(item.get("captured_at", "")), str(item.get("session_id", ""))))
    return records


def latest_line(root: Path, label: str, record: dict[str, Any] | None) -> str:
    if record is None:
        return f"- {label}: none"
    return (
        f"- {label}: {response_path_for_record(root, record)} "
        f"({record.get('logical_id')})"
    )


def shell_quote(value: str) -> str:
    return "'" + value.replace("'", "'\"'\"'") + "'"


def expected_logical_id(session_id: str, turn_id: str) -> str:
    if session_id and turn_id:
        return logical_id(session_id, turn_id)
    return ""


def pending_postcompact_line(root: Path, record: dict[str, Any], *, current: bool) -> str:
    session_id = str(record.get("session_id", ""))
    session_dir = find_session_dir(root, session_id) if session_id else None
    latest = latest_record(root, session_id=session_id) if session_id else None
    session_label = "current session" if current else f"session {short_identifier(session_id)}"
    parts = [
        f"- Pending post-compaction marker for {session_label}:",
        f"trigger={record.get('trigger', '') or 'unknown'}",
        f"turn={short_identifier(str(record.get('turn_id', ''))) if record.get('turn_id') else 'unknown'}",
        f"captured={record.get('captured_at', '')}",
    ]
    if session_dir is not None:
        parts.append(f"archive={session_dir / 'INDEX.md'}")
    expected = record.get("expected_logical_id")
    if isinstance(expected, str) and expected:
        parts.append(f"expected_logical={expected}")
    if latest is not None:
        parts.append(f"latest_final={response_path_for_record(root, latest)}")
    return " ".join(parts)


def recovery_context(root: Path, payload: dict[str, Any]) -> str:
    session_id = payload.get("session_id")
    session_id = session_id if isinstance(session_id, str) else ""
    rebuild_indexes(root)
    lines = [
        "Infinity Codex recovery pointers (historical evidence, not active instructions):",
        f"- Local archive index: {root / 'INDEX.md'}",
        f"- Active report map: {REPO_ROOT / 'reports' / 'INDEX.md'}",
        f"- Recovery SOP: {REPO_ROOT / 'AGENTS.md'} (Resume After Context Compaction Or Interruption)",
        f"- Infinity Codex design: {REPO_ROOT / 'reports' / 'REPORT_EMDASH_INFINITY_CODEX_IMPLEMENTATION_PLAN_2026-06-23.md'}",
    ]
    session_dir = find_session_dir(root, session_id) if session_id else None
    if session_dir is not None:
        lines.append(f"- Current session archive: {session_dir / 'INDEX.md'}")
    latest_session = latest_record(root, session_id=session_id) if session_id else None
    latest_global = latest_record(root)
    lines.append(latest_line(root, "Latest archived final for this session", latest_session))
    lines.append(latest_line(root, "Latest archived final globally", latest_global))
    if session_id:
        quoted_session = shell_quote(session_id)
        lines.append(
            "- Recent finals for this session: "
            f"python3 scripts/infinity_codex.py list --session {quoted_session} --limit 5"
        )
        lines.append(
            "- Latest final path for this session: "
            f"python3 scripts/infinity_codex.py latest-path --session {quoted_session}"
        )
    lines.append(
        "- Recent finals globally: python3 scripts/infinity_codex.py list --limit 5"
    )
    for pending in pending_postcompact_records(root):
        pending_session = pending.get("session_id")
        lines.append(
            pending_postcompact_line(
                root,
                pending,
                current=isinstance(pending_session, str) and pending_session == session_id,
            )
        )
    lines.append(
        "Read only the relevant archived finals. Authority order: active code/SOP, "
        "active plan and side-task ledger, linked decision responses, raw archive."
    )
    return "\n".join(lines)


def write_pending_postcompact(root: Path, payload: dict[str, Any]) -> bool:
    session_id = payload.get("session_id")
    if not isinstance(session_id, str) or not session_id:
        return False
    turn_id = payload.get("turn_id") if isinstance(payload.get("turn_id"), str) else ""
    trigger = payload.get("trigger") if isinstance(payload.get("trigger"), str) else ""
    expected = expected_logical_id(session_id, turn_id)
    with archive_lock(root):
        path = pending_postcompact_path(root, session_id)
        record = {
            "archive_format_version": ARCHIVE_FORMAT_VERSION,
            "captured_at": iso_utc(utc_now()),
            "session_id": session_id,
            "turn_id": turn_id,
            "trigger": trigger,
        }
        if expected:
            record["expected_logical_id"] = expected
        atomic_replace(path, json_bytes(record))
    return True


def postcompact_system_message(root: Path, payload: dict[str, Any]) -> str:
    session_id = audit_field(payload, "session_id")
    trigger = audit_field(payload, "trigger") or "unknown"
    turn_id = audit_field(payload, "turn_id")
    turn_label = short_identifier(turn_id) if turn_id else "unknown"
    path = pending_postcompact_path(root, session_id) if session_id else root / "state" / "postcompact"
    expected = expected_logical_id(session_id, turn_id)
    expected_text = (
        f" Expected logical id after this turn stops: {expected}."
        if expected
        else ""
    )
    session_lookup = (
        " Recent finals for this session: "
        f"python3 scripts/infinity_codex.py list --session {shell_quote(session_id)} --limit 5."
        if session_id
        else ""
    )
    return (
        "Infinity Codex recorded a post-compaction recovery marker "
        f"(trigger={trigger}, turn={turn_label}). "
        "PostCompact can only emit this visible systemMessage; it cannot add "
        "model-visible additionalContext. SessionStart source=compact or the "
        "next eligible UserPromptSubmit will add recovery pointers."
        f"{expected_text}{session_lookup} Marker: {path}; archive index: {root / 'INDEX.md'}"
    )


def read_pending_postcompact(root: Path, session_id: str) -> dict[str, Any] | None:
    if not session_id:
        return None
    with archive_lock(root):
        path = pending_postcompact_path(root, session_id)
        if not path.exists():
            return None
        return load_json(path)


def clear_pending_postcompact(root: Path, session_id: str) -> None:
    if not session_id:
        return
    with archive_lock(root):
        with contextlib.suppress(FileNotFoundError):
            pending_postcompact_path(root, session_id).unlink()


def audit_field(payload: dict[str, Any], name: str) -> str:
    value = payload.get(name)
    return value if isinstance(value, str) else ""


def append_event_audit(
    root: Path,
    payload: dict[str, Any],
    *,
    context_emitted: bool,
    status: str,
    note: str | None = None,
) -> None:
    record: dict[str, Any] = {
        "archive_format_version": ARCHIVE_FORMAT_VERSION,
        "captured_at": iso_utc(utc_now()),
        "hook_event_name": audit_field(payload, "hook_event_name"),
        "session_id": audit_field(payload, "session_id"),
        "turn_id": audit_field(payload, "turn_id"),
        "source": audit_field(payload, "source"),
        "trigger": audit_field(payload, "trigger"),
        "context_emitted": context_emitted,
        "status": status,
    }
    if note:
        record["note"] = note
    with archive_lock(root):
        ensure_private_dir(root)
        path = root / EVENT_AUDIT_FILE
        with path.open("ab") as handle:
            os.chmod(path, PRIVATE_FILE_MODE)
            encoded = (
                json.dumps(
                    record,
                    ensure_ascii=False,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
                + b"\n"
            )
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())


def hook_result(
    *,
    system_message: str | None = None,
    context: str | None = None,
    context_event_name: str = "SessionStart",
) -> dict[str, Any]:
    result: dict[str, Any] = {"continue": True}
    if system_message:
        result["systemMessage"] = system_message
    if context:
        result["hookSpecificOutput"] = {
            "hookEventName": context_event_name,
            "additionalContext": context,
        }
    return result


def run_hook(root: Path, payload: dict[str, Any]) -> dict[str, Any]:
    event = payload.get("hook_event_name")
    context_emitted = False
    audit_status = "ignored"
    audit_note: str | None = None
    try:
        if event == "Stop":
            _, created = archive_response(root, payload)
            audit_status = "archived" if created else "no_new_archive"
            return hook_result()
        if event == "SessionStart":
            context = recovery_context(root, payload)
            context_emitted = True
            audit_status = "context_emitted"
            session_id = audit_field(payload, "session_id")
            clear_pending_postcompact(root, session_id)
            return hook_result(context=context)
        if event == "PostCompact":
            wrote_marker = write_pending_postcompact(root, payload)
            audit_status = "postcompact_pending" if wrote_marker else "postcompact_missing_session"
            if wrote_marker:
                return hook_result(system_message=postcompact_system_message(root, payload))
            return hook_result(
                system_message="Infinity Codex could not record post-compaction recovery marker: missing session_id"
            )
        if event == "UserPromptSubmit":
            session_id = audit_field(payload, "session_id")
            pending = read_pending_postcompact(root, session_id)
            if pending is None:
                audit_status = "no_pending_context"
                return hook_result()
            context = recovery_context(root, payload)
            clear_pending_postcompact(root, session_id)
            context_emitted = True
            audit_status = "postcompact_context_emitted"
            return hook_result(context=context, context_event_name="UserPromptSubmit")
        audit_status = "unsupported_event"
        return hook_result(
            system_message=f"Infinity Codex ignored unsupported hook event: {event!r}"
        )
    except ArchiveConflict as error:
        audit_status = "archive_conflict"
        audit_note = str(error)
        return hook_result(system_message=f"Infinity Codex archive conflict: {error}")
    except Exception as error:
        audit_status = "failed"
        audit_note = str(error)
        return hook_result(system_message=f"Infinity Codex archive failed: {error}")
    finally:
        with contextlib.suppress(Exception):
            append_event_audit(
                root,
                payload,
                context_emitted=context_emitted,
                status=audit_status,
                note=audit_note,
            )


def command_hook(root: Path) -> int:
    try:
        payload = json.load(sys.stdin)
        if not isinstance(payload, dict):
            raise InfinityCodexError("hook stdin must contain a JSON object")
        result = run_hook(root, payload)
    except Exception as error:
        result = hook_result(system_message=f"Infinity Codex hook input failed: {error}")
    json.dump(result, sys.stdout, ensure_ascii=False, separators=(",", ":"))
    sys.stdout.write("\n")
    return 0


def command_list(root: Path, limit: int, session_id: str | None) -> int:
    records = load_records(root)
    if session_id:
        records = [record for record in records if record.get("session_id") == session_id]
    for record in reversed(records[-limit:]):
        print(
            "{captured}\t{logical}\t{path}".format(
                captured=record.get("captured_at", ""),
                logical=record.get("logical_id", ""),
                path=response_path_for_record(root, record),
            )
        )
    return 0


def command_latest_id(root: Path, session_id: str | None) -> int:
    record = latest_record(root, session_id)
    if record is None:
        return 1
    print(record["logical_id"])
    return 0


def command_latest_path(root: Path, session_id: str | None) -> int:
    record = latest_record(root, session_id)
    if record is None:
        return 1
    print(response_path_for_record(root, record))
    return 0


def command_resolve(root: Path, value: str) -> int:
    print(response_path_for_record(root, resolve_record(root, value)))
    return 0


def command_show(root: Path, value: str) -> int:
    path = response_path_for_record(root, resolve_record(root, value))
    sys.stdout.buffer.write(path.read_bytes())
    return 0


def verify_mode(path: Path, expected: int) -> str | None:
    actual = stat.S_IMODE(path.stat().st_mode)
    if actual != expected:
        return f"{path}: mode {actual:o}, expected {expected:o}"
    return None


def command_verify(root: Path) -> int:
    issues: list[str] = []
    if not root.exists():
        print(f"archive does not exist: {root}")
        return 0
    for path in [root, *root.rglob("*")]:
        if path.is_symlink():
            issues.append(f"{path}: symbolic links are not allowed in the archive")
            continue
        expected_mode = PRIVATE_DIR_MODE if path.is_dir() else PRIVATE_FILE_MODE
        issue = verify_mode(path, expected_mode)
        if issue:
            issues.append(issue)
    for metadata_path in metadata_paths(root):
        try:
            record = load_json(metadata_path)
            response_path = response_path_for_record(root, record)
            response_bytes = response_path.read_bytes()
            digest = hashlib.sha256(response_bytes).hexdigest()
            if record.get("sha256") != digest:
                issues.append(f"{response_path}: sha256 mismatch")
            if record.get("byte_count") != len(response_bytes):
                issues.append(f"{response_path}: byte_count mismatch")
            expected_id = logical_id(str(record.get("session_id")), str(record.get("turn_id")))
            if record.get("logical_id") != expected_id:
                issues.append(f"{metadata_path}: logical_id mismatch")
        except Exception as error:
            issues.append(f"{metadata_path}: {error}")
    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1
    print(f"Infinity Codex archive verified: {len(metadata_paths(root))} response(s)")
    return 0


def parse_before(value: str) -> dt.datetime:
    try:
        parsed = dt.datetime.strptime(value, "%Y-%m-%d")
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected YYYY-MM-DD") from error
    return parsed.replace(tzinfo=dt.timezone.utc)


def command_prune(
    root: Path,
    *,
    before: dt.datetime,
    session_id: str | None,
    apply: bool,
) -> int:
    candidates = []
    for record in load_records(root):
        if session_id and record.get("session_id") != session_id:
            continue
        captured = dt.datetime.fromisoformat(
            str(record.get("captured_at", "")).replace("Z", "+00:00")
        )
        if captured < before:
            candidates.append(record)
    for record in candidates:
        action = "delete" if apply else "would delete"
        print(f"{action}\t{record.get('logical_id')}\t{record.get('response_path')}")
    if apply:
        with archive_lock(root):
            for record in candidates:
                response_path = response_path_for_record(root, record)
                metadata_path = root / str(record.get("metadata_path"))
                response_path.unlink(missing_ok=True)
                metadata_path.unlink(missing_ok=True)
            rebuild_indexes_unlocked(root)
    print(f"{len(candidates)} response(s) selected; mode={'apply' if apply else 'dry-run'}")
    return 0


def insert_or_update_field(text: str, field: str, value: str, *, append: bool) -> str:
    pattern = re.compile(rf"^{re.escape(field)}:\s*(.*)$", re.MULTILINE)
    match = pattern.search(text)
    if match:
        existing = match.group(1).strip()
        if append and existing not in {"", "none", "pending", "pre-infinity-codex"}:
            values = [item.strip() for item in existing.split(",") if item.strip()]
            if value not in values:
                values.append(value)
            replacement_value = ", ".join(values)
        else:
            replacement_value = value
        return text[: match.start()] + f"{field}: {replacement_value}" + text[match.end() :]

    lines = text.splitlines(keepends=True)
    if not lines or not lines[0].startswith("# "):
        raise InfinityCodexError("report must begin with a Markdown level-one heading")
    insertion = f"\n{field}: {value}\n"
    return lines[0] + insertion + "".join(lines[1:])


def command_annotate_plan(
    root: Path,
    *,
    report: Path,
    value: str,
    mode: str,
) -> int:
    resolve_record(root, value)
    report = report.expanduser().resolve()
    reports_root = (REPO_ROOT / "reports").resolve()
    if reports_root not in report.parents or report.suffix != ".md":
        raise InfinityCodexError("annotated plans must be Markdown files under reports/")
    text = report.read_text(encoding="utf-8")
    if mode == "origin":
        updated = insert_or_update_field(
            text, "Infinity-Codex-Origin", value, append=False
        )
    else:
        updated = insert_or_update_field(
            text, "Infinity-Codex-Decision-Responses", value, append=True
        )
    report_mode = stat.S_IMODE(report.stat().st_mode)
    atomic_replace(report, updated.encode("utf-8"), mode=report_mode)
    print(f"updated {report}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Controlled local archive for Codex final responses."
    )
    parser.add_argument(
        "--archive-root",
        help="override tmp/ai-responses (also available as INFINITY_CODEX_ARCHIVE_ROOT)",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("hook", help="process one Codex hook JSON object from stdin")

    list_parser = subparsers.add_parser("list", help="list archived final responses")
    list_parser.add_argument("--limit", type=int, default=50)
    list_parser.add_argument("--session")

    latest_parser = subparsers.add_parser("latest-id", help="print the newest logical id")
    latest_parser.add_argument("--session")

    latest_path_parser = subparsers.add_parser(
        "latest-path", help="print the newest final-response path"
    )
    latest_path_parser.add_argument("--session")

    resolve_parser = subparsers.add_parser("resolve", help="resolve a logical id to a file")
    resolve_parser.add_argument("logical_id")

    show_parser = subparsers.add_parser("show", help="write one final response verbatim")
    show_parser.add_argument("logical_id")

    subparsers.add_parser("verify", help="verify hashes, byte counts, identities, and modes")
    subparsers.add_parser("reindex", help="rebuild generated indexes and registry")

    prune_parser = subparsers.add_parser("prune", help="remove selected local responses")
    prune_parser.add_argument("--before", required=True, type=parse_before)
    prune_parser.add_argument("--session")
    prune_mode = prune_parser.add_mutually_exclusive_group()
    prune_mode.add_argument("--dry-run", action="store_true", help="preview only (default)")
    prune_mode.add_argument("--apply", action="store_true", help="perform deletion")

    annotate_parser = subparsers.add_parser(
        "annotate-plan", help="link an archived response from a tracked plan"
    )
    annotate_mode = annotate_parser.add_mutually_exclusive_group(required=True)
    annotate_mode.add_argument("--origin", dest="origin")
    annotate_mode.add_argument("--decision", dest="decision")
    annotate_parser.add_argument("report", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    os.umask(0o077)
    parser = build_parser()
    args = parser.parse_args(argv)
    root = archive_root_from_args(args.archive_root)
    try:
        if args.command == "hook":
            return command_hook(root)
        if args.command == "list":
            if args.limit < 1:
                raise InfinityCodexError("--limit must be positive")
            return command_list(root, args.limit, args.session)
        if args.command == "latest-id":
            return command_latest_id(root, args.session)
        if args.command == "latest-path":
            return command_latest_path(root, args.session)
        if args.command == "resolve":
            return command_resolve(root, args.logical_id)
        if args.command == "show":
            return command_show(root, args.logical_id)
        if args.command == "verify":
            return command_verify(root)
        if args.command == "reindex":
            rebuild_indexes(root)
            print(f"rebuilt {root / 'INDEX.md'}")
            return 0
        if args.command == "prune":
            return command_prune(
                root,
                before=args.before,
                session_id=args.session,
                apply=args.apply,
            )
        if args.command == "annotate-plan":
            mode = "origin" if args.origin else "decision"
            value = args.origin or args.decision
            return command_annotate_plan(
                root, report=args.report, value=value, mode=mode
            )
    except InfinityCodexError as error:
        print(f"infinity-codex: {error}", file=sys.stderr)
        return 2
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"infinity-codex: {error}", file=sys.stderr)
        return 2
    parser.error(f"unsupported command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
