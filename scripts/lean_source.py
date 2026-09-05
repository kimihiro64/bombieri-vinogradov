"""Validate Lean source policy and the Palomar boundary."""

from __future__ import annotations

import json
import re
from collections.abc import Sequence
from pathlib import Path
from typing import Final

FORBIDDEN_LEAN: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*(?:axiom|constant|opaque)\b|\b(?:sorry|admit|native_decide)\b"
)
FORBIDDEN_CHALLENGE: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*(?:axiom|constant|opaque)\b|\b(?:admit|native_decide)\b"
)
DISCOVERY_LEAN: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*#(?:check|print|eval|reduce)\b|"
    r"\b(?:exact|apply|simp|rw|aesop)\?|\blibrary_search\b"
)
BROAD_IMPORT: Final[re.Pattern[str]] = re.compile(r"(?m)^\s*import\s+(?:Batteries|Mathlib)\s*$")
AUTO_IMPLICIT_FALSE: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*set_option\s+autoImplicit\s+false\s*$"
)
REVIEWED_NOLINT_CLASSES: Final[frozenset[str]] = frozenset(
    {"docBlame", "simpNF", "unusedArguments"}
)


class LeanSourceError(RuntimeError):
    """Raised when Lean source or a Palomar boundary violates policy."""


def check_nolints_baseline(root: Path) -> None:
    """Validate the reviewed declaration-level Lean linter migration baseline."""
    path = root / "scripts" / "nolints.json"
    try:
        baseline = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise LeanSourceError(f"Lean nolint baseline cannot be read: {error}") from error

    failures: list[str] = []
    if not isinstance(baseline, list) or not baseline:
        failures.append("scripts/nolints.json must be a nonempty JSON list")
    else:
        seen: set[tuple[str, str]] = set()
        for index, row in enumerate(baseline):
            if (
                not isinstance(row, list)
                or len(row) != 2
                or not all(isinstance(item, str) and item.strip() for item in row)
            ):
                failures.append(f"row {index} must contain two nonempty strings")
                continue
            linter, declaration = row
            key = (linter, declaration)
            if key in seen:
                failures.append(f"duplicate row {index}: {linter} / {declaration}")
            seen.add(key)
            if linter not in REVIEWED_NOLINT_CLASSES:
                failures.append(f"row {index} uses unreviewed linter class {linter}")
    if failures:
        raise LeanSourceError("Lean nolint baseline failed:\n" + "\n".join(failures))
    print(f"Lean nolint baseline: clean ({len(baseline)} reviewed declarations)")


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean comments while preserving line structure."""
    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index : index + 2]
        character = source[index]
        if depth > 0:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                output.extend("  ")
                index += 2
                continue
            output.append("\n" if character == "\n" else " ")
            index += 1
            continue
        if not in_string and pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
            continue
        if not in_string and pair == "--":
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
            continue
        output.append(character)
        if in_string:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
        elif character == '"':
            in_string = True
        index += 1
    if depth != 0:
        raise LeanSourceError("unterminated Lean block comment")
    return "".join(output)


def lean_imports(code: str) -> list[str]:
    """Return direct import names from a Lean source."""
    return re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_'.]+)\s*$", code)


def check_lean_sources(root: Path, candidates: Sequence[str]) -> None:
    """Check public Lean source policy without requiring a Lean runtime."""
    failures: list[str] = []
    files = [
        root / relative
        for relative in candidates
        if relative.endswith(".lean") and (root / relative).is_file()
    ]
    for path in files:
        relative = path.relative_to(root).as_posix()
        source = path.read_text(encoding="utf-8")
        try:
            code = strip_lean_comments(source)
        except LeanSourceError as error:
            failures.append(f"{relative}: {error}")
            continue
        forbidden = FORBIDDEN_CHALLENGE if relative == "Challenge.lean" else FORBIDDEN_LEAN
        if match := forbidden.search(code):
            failures.append(f"{relative}: forbidden Lean source `{match.group(0).strip()}`")
        if match := DISCOVERY_LEAN.search(code):
            failures.append(f"{relative}: discovery command `{match.group(0).strip()}`")
        if match := BROAD_IMPORT.search(code):
            failures.append(f"{relative}: broad import `{match.group(0).strip()}`")
        imports = lean_imports(code)
        if imports != sorted(imports):
            failures.append(f"{relative}: imports are not in ordinal order")
        if len(imports) != len(set(imports)):
            failures.append(f"{relative}: duplicate direct import")
        if relative not in {"Challenge.lean", "Solution.lean"} and "/-!" not in source:
            failures.append(f"{relative}: missing module documentation")
    challenge = root / "Challenge.lean"
    if challenge.exists():
        size = challenge.stat().st_size
        lines = len(challenge.read_text(encoding="utf-8").splitlines())
        if size > 100 * 1024 or lines > 1000:
            failures.append(f"Challenge.lean exceeds 100 KiB or 1,000 lines ({size}, {lines})")
        elif size > 32 * 1024 or lines > 300:
            print(f"warning: Challenge.lean exceeds the preferred audit size ({size}, {lines})")
    if failures:
        raise LeanSourceError("Lean source policy failed:\n" + "\n".join(failures))
    print(f"Lean source policy: clean ({len(files)} files)")


def check_palomar_boundary(root: Path) -> None:
    """Enforce cheap syntax-level Palomar theorem-boundary invariants."""
    failures: list[str] = []
    boundary: dict[str, tuple[str, list[str]]] = {}
    for relative in ("Challenge.lean", "Solution.lean"):
        path = root / relative
        if not path.is_file():
            failures.append(f"{relative}: missing boundary module")
            continue
        source = path.read_text(encoding="utf-8")
        try:
            code = strip_lean_comments(source)
        except LeanSourceError as error:
            failures.append(f"{relative}: {error}")
            continue
        imports = lean_imports(code)
        boundary[relative] = (code, imports)
        if AUTO_IMPLICIT_FALSE.search(code) is None:
            failures.append(f"{relative}: must contain `set_option autoImplicit false`")

    challenge_imports = boundary.get("Challenge.lean", ("", []))[1]
    solution_imports = boundary.get("Solution.lean", ("", []))[1]
    for module in challenge_imports:
        if not module.startswith("Mathlib."):
            failures.append(
                f"Challenge.lean: Palomar boundary import `{module}` is not an exact Mathlib module"
            )
    for module in sorted(set(challenge_imports) - set(solution_imports)):
        failures.append(
            f"Solution.lean: missing Challenge's direct Mathlib type-provider import `{module}`"
        )

    config_path = root / "comparator.json"
    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        failures.append(f"comparator.json: cannot read valid JSON: {error}")
    else:
        if config.get("challenge_module") != "Challenge":
            failures.append("comparator.json: challenge_module must be `Challenge`")
        if config.get("solution_module") != "Solution":
            failures.append("comparator.json: solution_module must be `Solution`")
        declarations = [
            *config.get("theorem_names", []),
            *config.get("definition_names", []),
        ]
        if not declarations or not all(
            isinstance(name, str) and name.strip() for name in declarations
        ):
            failures.append("comparator.json: declaration list must be nonempty strings")

    if failures:
        raise LeanSourceError("Palomar boundary policy failed:\n" + "\n".join(failures))
    print(
        "Palomar boundary: Mathlib-only Challenge, explicit autoImplicit, "
        "and mirrored provider imports"
    )
