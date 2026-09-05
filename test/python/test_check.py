from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from scripts.check import (
    CheckFailure,
    check_lean_sources,
    check_palomar_boundary,
    check_submission_link,
    is_private_path,
    lean_imports,
    public_candidate_paths,
    strip_lean_comments,
    tracked_public_size,
)
from scripts.import_graph import detect_cycles, transitive_dependents


def test_private_path_boundary_is_component_aware() -> None:
    assert is_private_path(".research/GOAL.json")
    assert is_private_path("AGENTS.md")
    assert not is_private_path("scripts/research_experiment.py")
    assert not is_private_path("AGENTS.md.example")


def test_nested_lean_comments_are_removed() -> None:
    source = "theorem ok : True := by\n  /- sorry /- admit -/ -/ trivial\n"
    stripped = strip_lean_comments(source)
    assert "sorry" not in stripped
    assert "admit" not in stripped
    assert "trivial" in stripped
    assert stripped.count("\n") == source.count("\n")


def test_import_parser_ignores_comments() -> None:
    source = strip_lean_comments("/- import Mathlib -/\nimport Mathlib.Data.Nat.Basic\n")
    assert lean_imports(source) == ["Mathlib.Data.Nat.Basic"]


def test_dependency_cycle_detection() -> None:
    graph = {"A": {"B"}, "B": {"C"}, "C": {"A"}}
    assert detect_cycles(graph) == [["A", "B", "C", "A"]]


def test_transitive_blast_radius() -> None:
    graph = {"A": set(), "B": {"A"}, "C": {"B"}, "D": {"A"}}
    impact = transitive_dependents(graph)
    assert impact["A"] == {"B", "C", "D"}
    assert impact["B"] == {"C"}


def test_ignored_artifact_does_not_affect_tracked_size(tmp_path: Path) -> None:
    tracked = tmp_path / "tracked.txt"
    ignored = tmp_path / ".lake" / "large.bin"
    ignored.parent.mkdir()
    tracked.write_bytes(b"abc")
    ignored.write_bytes(b"x" * 10000)
    assert tracked_public_size(tmp_path, ["tracked.txt"]) == 3


def test_ignored_private_lean_does_not_affect_public_policy(tmp_path: Path) -> None:
    (tmp_path / ".gitignore").write_text(".research/\n", encoding="utf-8")
    (tmp_path / "Example.lean").write_text(
        "/-! Public module. -/\nimport Mathlib.Data.Nat.Basic\n",
        encoding="utf-8",
    )
    deleted = tmp_path / "Deleted.lean"
    deleted.write_text("axiom obsolete : False\n", encoding="utf-8")
    private = tmp_path / ".research" / "Private.lean"
    private.parent.mkdir()
    private.write_text("axiom privateLeak : False\n", encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    subprocess.run(
        ["git", "add", ".gitignore", "Example.lean", "Deleted.lean"],
        cwd=tmp_path,
        check=True,
    )
    deleted.unlink()
    candidates = public_candidate_paths(tmp_path)
    assert ".research/Private.lean" not in candidates
    assert "Deleted.lean" not in candidates
    check_lean_sources(tmp_path)


def test_submission_link_accepts_current_form(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text(
        "Submit at https://submit.palomar-registry.org/.\n", encoding="utf-8"
    )
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    check_submission_link(tmp_path)


def test_submission_link_rejects_missing_current_form(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text("No submission link.\n", encoding="utf-8")
    with pytest.raises(CheckFailure, match="README.md must link"):
        check_submission_link(tmp_path)


def test_submission_link_rejects_retired_form(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text(
        "https://submit.palomar-registry.org/\nPalomarSubmission/issues/new\n",
        encoding="utf-8",
    )
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    with pytest.raises(CheckFailure, match="retired Palomar form"):
        check_submission_link(tmp_path)


def write_boundary_fixture(tmp_path: Path, challenge_import: str) -> None:
    (tmp_path / "Challenge.lean").write_text(
        f"import {challenge_import}\n\n"
        "set_option autoImplicit false\n\n"
        "theorem Boundary.result : True := by\n  sorry\n",
        encoding="utf-8",
    )
    (tmp_path / "Solution.lean").write_text(
        "import Mathlib.Data.Nat.Basic\n\n"
        "set_option autoImplicit false\n\n"
        "theorem Boundary.result : True := by\n  trivial\n",
        encoding="utf-8",
    )
    (tmp_path / "comparator.json").write_text(
        json.dumps(
            {
                "challenge_module": "Challenge",
                "solution_module": "Solution",
                "theorem_names": ["Boundary.result"],
                "definition_names": [],
            }
        ),
        encoding="utf-8",
    )


def test_palomar_boundary_accepts_mathlib_only_challenge(tmp_path: Path) -> None:
    write_boundary_fixture(tmp_path, "Mathlib.Data.Nat.Basic")
    check_palomar_boundary(tmp_path)


def test_palomar_boundary_rejects_project_import(tmp_path: Path) -> None:
    write_boundary_fixture(tmp_path, "Project.Statement")
    with pytest.raises(CheckFailure, match="is not an exact Mathlib module"):
        check_palomar_boundary(tmp_path)


def test_palomar_boundary_rejects_missing_auto_implicit_guard(tmp_path: Path) -> None:
    write_boundary_fixture(tmp_path, "Mathlib.Data.Nat.Basic")
    solution = tmp_path / "Solution.lean"
    solution.write_text(
        solution.read_text(encoding="utf-8").replace("set_option autoImplicit false\n\n", ""),
        encoding="utf-8",
    )
    with pytest.raises(CheckFailure, match="Solution.lean: must contain"):
        check_palomar_boundary(tmp_path)
