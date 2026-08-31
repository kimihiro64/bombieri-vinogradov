from __future__ import annotations

from pathlib import Path

from scripts.check import is_private_path, lean_imports, strip_lean_comments, tracked_public_size
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
