from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.boundary_audit import (
    BoundaryAuditFailure,
    load_configuration,
    probe_source,
    require_boundary_source_policy,
    require_equal_exports,
)


def test_probe_audits_raw_types_and_internal_definition_values() -> None:
    source = probe_source("Challenge", ["Example.result"])
    assert "reprStr info.type" in source
    assert "reprStr value.value" in source
    assert "#audit_boundary Example.result" in source


def test_configuration_accepts_root_level_declarations(tmp_path: Path) -> None:
    (tmp_path / "comparator.json").write_text(
        json.dumps(
            {
                "challenge_module": "Challenge",
                "solution_module": "Solution",
                "theorem_names": ["Example.result"],
                "definition_names": ["pi", "BombieriVinogradov"],
            }
        ),
        encoding="utf-8",
    )
    _, _, declarations = load_configuration(tmp_path)
    assert declarations == ["Example.result", "pi", "BombieriVinogradov"]
    source = probe_source("Challenge", declarations)
    assert "#audit_boundary pi" in source
    assert "#audit_boundary BombieriVinogradov" in source


def test_equal_exports_are_accepted() -> None:
    records = (
        "BOUNDARY-ROOT|Example.result",
        "BOUNDARY-TYPE|Example.result|Example.result|Lean.Expr.sort (Lean.Level.zero)",
    )
    require_equal_exports(records, records)


def test_different_elaborated_exports_are_rejected() -> None:
    challenge = ("BOUNDARY-TYPE|Example.result|Example.result|implicit proposition",)
    solution = ("BOUNDARY-TYPE|Example.result|Example.result|Mathlib constant",)
    with pytest.raises(BoundaryAuditFailure, match="exports differ"):
        require_equal_exports(challenge, solution)


def test_solution_must_directly_import_challenge_mathlib_providers(tmp_path: Path) -> None:
    (tmp_path / "Challenge.lean").write_text(
        "import Mathlib.NumberTheory.PrimeCounting\n\nset_option autoImplicit false\n",
        encoding="utf-8",
    )
    (tmp_path / "Solution.lean").write_text(
        "import Example.Statement\n\nset_option autoImplicit false\n",
        encoding="utf-8",
    )
    with pytest.raises(BoundaryAuditFailure, match="lacks direct Mathlib provider imports"):
        require_boundary_source_policy(tmp_path, "Challenge", "Solution")


def test_boundary_provider_imports_and_autoimplicit_are_accepted(tmp_path: Path) -> None:
    shared = "import Mathlib.NumberTheory.PrimeCounting\n\nset_option autoImplicit false\n"
    (tmp_path / "Challenge.lean").write_text(shared, encoding="utf-8")
    (tmp_path / "Solution.lean").write_text(
        "import Example.Statement\n" + shared,
        encoding="utf-8",
    )
    require_boundary_source_policy(tmp_path, "Challenge", "Solution")
