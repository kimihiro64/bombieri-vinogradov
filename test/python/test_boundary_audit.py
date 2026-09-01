from __future__ import annotations

import pytest

from scripts.boundary_audit import BoundaryAuditFailure, probe_source, require_equal_exports


def test_probe_audits_raw_types_and_internal_definition_values() -> None:
    source = probe_source("Challenge", ["Example.result"])
    assert "reprStr info.type" in source
    assert "reprStr value.value" in source
    assert "#audit_boundary Example.result" in source


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
