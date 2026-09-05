"""Validate the auxiliary doc-gen4 workspace dependency closure."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import TypedDict, cast


class ManifestClosureError(RuntimeError):
    """Raised when the documentation manifest is stale or malformed."""


class Package(TypedDict, total=False):
    """Fields used from a Lake manifest package record."""

    type: str
    name: str
    url: str
    rev: str
    dir: str


class Manifest(TypedDict):
    """Fields used from a Lake manifest."""

    name: str
    packages: list[Package]


def load_manifest(path: Path) -> Manifest:
    """Load and minimally validate one Lake manifest."""
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ManifestClosureError(f"cannot read {path}: {error}") from error
    if not isinstance(raw, dict):
        raise ManifestClosureError(f"{path}: expected a JSON object")
    name = raw.get("name")
    packages = raw.get("packages")
    if not isinstance(name, str) or not isinstance(packages, list):
        raise ManifestClosureError(f"{path}: missing name or packages")
    if not all(isinstance(package, dict) for package in packages):
        raise ManifestClosureError(f"{path}: package entries must be objects")
    return cast(Manifest, raw)


def normalize_git_url(url: str) -> str:
    """Normalize superficial Git URL spelling differences."""
    normalized = url.strip().rstrip("/")
    if normalized.lower().endswith(".git"):
        normalized = normalized[:-4]
    return normalized.lower()


def git_identity(package: Package, source: Path) -> tuple[str, str]:
    """Return the immutable repository and revision identity of a Git package."""
    url = package.get("url")
    revision = package.get("rev")
    if not isinstance(url, str) or not isinstance(revision, str):
        raise ManifestClosureError(f"{source}: Git package lacks url or rev")
    return normalize_git_url(url), revision


def check_manifest_closure(root: Path) -> None:
    """Require docbuild to contain the root path package and every Git dependency."""
    root_path = root / "lake-manifest.json"
    docs_path = root / "docbuild" / "lake-manifest.json"
    root_manifest = load_manifest(root_path)
    docs_manifest = load_manifest(docs_path)

    root_entry = [
        package
        for package in docs_manifest["packages"]
        if package.get("type") == "path"
        and package.get("name") == root_manifest["name"]
        and package.get("dir") == "../"
    ]
    if len(root_entry) != 1:
        raise ManifestClosureError(
            f"{docs_path}: expected one ../ path entry for {root_manifest['name']}"
        )

    required = {
        git_identity(package, root_path): package.get("name", "<unnamed>")
        for package in root_manifest["packages"]
        if package.get("type") == "git"
    }
    documented = {
        git_identity(package, docs_path)
        for package in docs_manifest["packages"]
        if package.get("type") == "git"
    }
    missing = sorted(name for identity, name in required.items() if identity not in documented)
    if missing:
        joined = ", ".join(missing)
        raise ManifestClosureError(
            f"{docs_path}: missing root dependencies: {joined}; "
            "run lake update from docbuild and commit the manifest"
        )

    print(f"documentation manifest: clean ({len(required)} root Git dependencies covered)")


def main() -> int:
    """Validate the repository containing this script."""
    root = Path(__file__).resolve().parents[1]
    try:
        check_manifest_closure(root)
    except ManifestClosureError as error:
        print(f"documentation manifest check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
