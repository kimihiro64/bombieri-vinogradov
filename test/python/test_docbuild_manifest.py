from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.check_docbuild_manifest import ManifestClosureError, check_manifest_closure


def write_manifests(root: Path, *, include_dependency: bool = True) -> None:
    """Write a minimal root and auxiliary Lake manifest pair."""
    dependency = {
        "type": "git",
        "name": "Dependency",
        "url": "https://example.com/Dependency.git",
        "rev": "abc123",
    }
    root_manifest = {
        "name": "Example",
        "packages": [dependency],
    }
    docs_packages = [
        {
            "type": "path",
            "name": "Example",
            "dir": "../",
        }
    ]
    if include_dependency:
        docs_packages.append(dependency)
    docs_manifest = {
        "name": "docbuild",
        "packages": docs_packages,
    }
    (root / "docbuild").mkdir()
    (root / "lake-manifest.json").write_text(json.dumps(root_manifest), encoding="utf-8")
    (root / "docbuild" / "lake-manifest.json").write_text(
        json.dumps(docs_manifest), encoding="utf-8"
    )


def test_manifest_closure_accepts_root_dependencies(tmp_path: Path) -> None:
    write_manifests(tmp_path)
    check_manifest_closure(tmp_path)


def test_manifest_closure_rejects_stale_docs_manifest(tmp_path: Path) -> None:
    write_manifests(tmp_path, include_dependency=False)
    with pytest.raises(ManifestClosureError, match="missing root dependencies: Dependency"):
        check_manifest_closure(tmp_path)


def test_manifest_closure_requires_root_path_entry(tmp_path: Path) -> None:
    write_manifests(tmp_path)
    docs_path = tmp_path / "docbuild" / "lake-manifest.json"
    manifest = json.loads(docs_path.read_text(encoding="utf-8"))
    manifest["packages"][0]["dir"] = "../../wrong"
    docs_path.write_text(json.dumps(manifest), encoding="utf-8")
    with pytest.raises(ManifestClosureError, match="expected one ../ path entry"):
        check_manifest_closure(tmp_path)
