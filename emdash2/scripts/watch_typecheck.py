#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


IGNORE_DIRS = {
    ".git",
    ".scratchpad",
    "_build",
    ".lambdapi",
    ".cache",
    "logs",
}


@dataclass(frozen=True)
class FileStamp:
    mtime_ns: int
    size: int


def iter_watched_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in IGNORE_DIRS]
        p = Path(dirpath)
        for name in filenames:
            if name == "lambdapi.pkg" or name.endswith(".lp"):
                files.append(p / name)
    return sorted(files)


def snapshot(files: list[Path]) -> dict[Path, FileStamp]:
    snap: dict[Path, FileStamp] = {}
    for f in files:
        try:
            st = f.stat()
        except FileNotFoundError:
            continue
        snap[f] = FileStamp(mtime_ns=st.st_mtime_ns, size=st.st_size)
    return snap


def changed(prev: dict[Path, FileStamp], curr: dict[Path, FileStamp]) -> bool:
    if prev.keys() != curr.keys():
        return True
    for k, v in curr.items():
        if prev.get(k) != v:
            return True
    return False


def clear_screen() -> None:
    sys.stdout.write("\033[2J\033[H")
    sys.stdout.flush()


def run_check(log_path: Path | None) -> int:
    cmd = ["bash", "-lc", "./scripts/check.sh"]
    if log_path is None:
        proc = subprocess.run(cmd)
        return proc.returncode

    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("a", encoding="utf-8") as f:
        f.write(f"\n=== typecheck @ {time.strftime('%Y-%m-%d %H:%M:%S %z')} ===\n")
        f.flush()
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT)
        f.write(f"=== exit {proc.returncode} ===\n")
        f.flush()
        return proc.returncode


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Watch *.lp and lambdapi.pkg; re-run Lambdapi typecheck on changes."
    )
    ap.add_argument(
        "--interval",
        type=float,
        default=0.4,
        help="Polling interval in seconds (default: 0.4).",
    )
    ap.add_argument(
        "--log",
        type=Path,
        default=None,
        help="Append output to a log file (e.g. logs/typecheck.log).",
    )
    ap.add_argument(
        "--no-clear",
        action="store_true",
        help="Do not clear the terminal before each check.",
    )
    ap.add_argument(
        "--once",
        action="store_true",
        help="Run one check and exit.",
    )
    args = ap.parse_args()

    root = Path(".").resolve()
    files = iter_watched_files(root)
    prev = snapshot(files)

    if not args.no_clear:
        clear_screen()
    print(f"Watching {len(files)} file(s). Interval={args.interval}s. Ctrl-C to stop.")
    rc = run_check(args.log)
    if args.once:
        return rc

    try:
        while True:
            time.sleep(args.interval)
            files = iter_watched_files(root)
            curr = snapshot(files)
            if not changed(prev, curr):
                continue
            prev = curr
            if not args.no_clear:
                clear_screen()
            print(f"Change detected @ {time.strftime('%H:%M:%S')}. Re-checking…")
            rc = run_check(args.log)
            print(f"Done (exit {rc}).")
    except KeyboardInterrupt:
        print("\nStopped.")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())

