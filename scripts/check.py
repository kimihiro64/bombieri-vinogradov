"""Run public repository quality and release checks."""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path
from typing import Final

ROOT = Path(__file__).resolve().parent.parent
if __package__ in {None, ""}:
    sys.path.insert(0, str(ROOT))

from scripts.lean_source import (  # noqa: E402
    LeanSourceError,
    check_lean_sources,
    check_nolints_baseline,
    check_palomar_boundary,
)

PRIVATE_PATHS: Final[tuple[str, ...]] = (
    ".agents",
    ".research",
    ".codex",
    "AGENTS.md",
    "PLANS.md",
    "AI_HANDOFF.md",
    "ACTIVE_PROOF_STATE.md",
)
MAX_PUBLIC_BYTES: Final[int] = 500 * 1024 * 1024
PALOMAR_SUBMISSION_URL: Final[str] = "https://submit.palomar-registry.org/"
RETIRED_PALOMAR_FORM: Final[str] = "PalomarSubmission/issues/new"


class CheckFailure(RuntimeError):  # noqa: N818
    """Raised when a repository invariant fails."""


def repository_root() -> Path:
    """Return the repository root containing this script."""
    return Path(__file__).resolve().parent.parent


def run(command: Sequence[str], root: Path, *, capture: bool = False) -> str:
    """Run one command and fail with a compact diagnostic."""
    result = subprocess.run(
        list(command),
        cwd=root,
        check=False,
        text=True,
        capture_output=capture,
    )
    if result.returncode != 0:
        detail = (result.stdout or "") + (result.stderr or "")
        raise CheckFailure(f"command failed ({result.returncode}): {' '.join(command)}\n{detail}")
    return result.stdout if capture else ""


def tracked_paths(root: Path) -> list[str]:
    """Return normalized paths in the Git index."""
    output = run(("git", "ls-files", "-z"), root, capture=True)
    return [item.replace("\\", "/") for item in output.split("\0") if item]


def public_candidate_paths(root: Path) -> list[str]:
    """Return tracked and nonignored untracked paths visible to public checks."""
    output = run(
        ("git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"),
        root,
        capture=True,
    )
    normalized = {item.replace("\\", "/") for item in output.split("\0") if item}
    return sorted(relative for relative in normalized if (root / relative).is_file())


def is_private_path(path: str) -> bool:
    """Return whether a repository-relative path belongs to the private layer."""
    normalized = path.strip("/").replace("\\", "/")
    return any(normalized == item or normalized.startswith(f"{item}/") for item in PRIVATE_PATHS)


def tracked_public_size(root: Path, paths: Sequence[str]) -> int:
    """Return the size of tracked regular nonsymlink files only."""
    total = 0
    for relative in paths:
        path = root / relative
        if path.is_file() and not path.is_symlink():
            total += path.stat().st_size
    return total


def check_public_boundary(root: Path) -> None:
    """Reject private paths in the public Git index and oversize exports."""
    tracked = tracked_paths(root)
    leaked = sorted(path for path in tracked if is_private_path(path))
    if leaked:
        raise CheckFailure("private paths are tracked:\n" + "\n".join(leaked))

    total = tracked_public_size(root, tracked)
    if total > MAX_PUBLIC_BYTES:
        raise CheckFailure(f"public tree is {total} bytes; limit is {MAX_PUBLIC_BYTES}")
    print(f"public boundary: clean ({len(tracked)} tracked paths, {total} bytes)")


def check_architecture(root: Path) -> None:
    """Run the public dependency and file-size architecture audit."""
    run((sys.executable, "scripts/import_graph.py"), root)


def check_documentation_manifest(root: Path) -> None:
    """Require the documentation workspace to cover the project dependency closure."""
    run((sys.executable, "scripts/check_docbuild_manifest.py"), root)


def check_submission_link(root: Path) -> None:
    """Require the current Palomar form and reject its retired predecessor."""
    readme = (root / "README.md").read_bytes()
    if PALOMAR_SUBMISSION_URL.encode("ascii") not in readme:
        raise CheckFailure(f"README.md must link to {PALOMAR_SUBMISSION_URL}")
    retired = []
    retired_needle = RETIRED_PALOMAR_FORM.encode("ascii")
    for relative in tracked_paths(root):
        if not relative.lower().endswith(".md"):
            continue
        if retired_needle in (root / relative).read_bytes():
            retired.append(relative)
    if retired:
        raise CheckFailure("retired Palomar form appears in:\n" + "\n".join(retired))
    print("submission link: current")


def check_metadata(root: Path, *, release: bool) -> None:
    """Run Palomar's metadata validator in template or submission mode."""
    metadata = (root / "formalization.yaml").read_text(encoding="utf-8")
    template_mode = "TEMPLATE:" in metadata
    if release and template_mode:
        raise CheckFailure("release profile forbids TEMPLATE values in formalization.yaml")
    ruby = shutil.which("ruby")
    if ruby is None:
        if release:
            raise CheckFailure("Ruby is required for release metadata validation")
        print("metadata: skipped Ruby validator (Ruby not installed)")
        return
    test_path = root / "test" / "validate_formalization_test.rb"
    if test_path.is_file():
        run((ruby, "test/validate_formalization_test.rb"), root)
        print("metadata validator tests: clean")
    command = [ruby, "scripts/validate-formalization.rb"]
    if template_mode:
        command.append("--expect-template")
    run(command, root)
    print(f"metadata: {'template' if template_mode else 'submission'} mode valid")


def check_python(root: Path) -> None:
    """Run Python formatter, linter, type checker, and tests."""
    commands = (
        (sys.executable, "-m", "ruff", "format", "--check", "scripts", "test/python"),
        (sys.executable, "-m", "ruff", "check", "scripts", "test/python"),
        (sys.executable, "-m", "mypy", "scripts", "test/python"),
        (sys.executable, "-m", "pytest"),
    )
    for command in commands:
        run(command, root)
    print("Python quality: clean")


def check_lean_build(root: Path) -> None:
    """Build and lint the complete pinned Lean project."""
    lake = shutil.which("lake")
    if lake is None:
        raise CheckFailure("lake is required for the research and release profiles")
    run((lake, "build"), root)
    run((lake, "lint"), root)
    print("Lean build and lint: clean")


def check_release_git(root: Path) -> None:
    """Require a clean exact commit and GitHub origin for release."""
    status = run(("git", "status", "--porcelain=v1"), root, capture=True)
    if status:
        raise CheckFailure("release requires a clean worktree")
    head = run(("git", "rev-parse", "HEAD"), root, capture=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        raise CheckFailure("release HEAD is not a full 40-character commit")
    origin = run(("git", "remote", "get-url", "origin"), root, capture=True).strip()
    if "github.com" not in origin.lower():
        raise CheckFailure("release origin must be a GitHub repository")
    print(f"release Git state: clean at {head}")


def check_release_documents(root: Path) -> None:
    """Reject starter prose and unresolved scaffold tokens at release."""
    markers = (
        "TEMPLATE:",
        "__PROJECT_",
        "__PROBLEM_",
        "__AUTHOR_",
        "__REPOSITORY_",
        "Replace with",
        "Replace this scaffold",
        "initially contain a clearly marked wiring theorem",
    )
    paths = (root / "README.md", root / "CITATION.cff", root / "paper" / "research-paper.tex")
    failures: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for marker in markers:
            if marker in text:
                failures.append(
                    f"{path.relative_to(root).as_posix()}: unresolved marker {marker!r}"
                )
    if failures:
        raise CheckFailure("release documents are incomplete:\n" + "\n".join(failures))
    print("release documents: no scaffold markers")


def parse_arguments(arguments: Sequence[str] | None = None) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", choices=("fast", "research", "release"), default="fast")
    return parser.parse_args(arguments)


def main(arguments: Sequence[str] | None = None) -> int:
    """Run the selected quality profile."""
    options = parse_arguments(arguments)
    root = repository_root()
    try:
        check_public_boundary(root)
        check_documentation_manifest(root)
        check_submission_link(root)
        check_lean_sources(root, public_candidate_paths(root))
        check_nolints_baseline(root)
        check_palomar_boundary(root)
        check_architecture(root)
        check_metadata(root, release=options.profile == "release")
        if options.profile in {"research", "release"}:
            check_python(root)
            check_lean_build(root)
        if options.profile == "release":
            check_release_documents(root)
            check_release_git(root)
    except (CheckFailure, LeanSourceError) as error:
        print(f"check failed: {error}", file=sys.stderr)
        return 1
    print(f"{options.profile} profile passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
