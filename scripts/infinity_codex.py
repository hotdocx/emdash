#!/usr/bin/env python3
"""Compatibility launcher for a Codex hook cached before nested-root repair."""

from __future__ import annotations

import os
import sys
from pathlib import Path


TARGET = (
    Path(__file__).resolve().parent.parent
    / "emdash2"
    / "scripts"
    / "infinity_codex.py"
)

if not TARGET.is_file():
    raise SystemExit(f"Infinity Codex target not found: {TARGET}")

os.execv(sys.executable, [sys.executable, str(TARGET), *sys.argv[1:]])
