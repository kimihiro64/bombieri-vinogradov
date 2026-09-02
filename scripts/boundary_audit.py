"""Compare elaborated Palomar declaration types before the full Lean build."""

from __future__ import annotations

import difflib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Final

LEAN_NAME: Final[re.Pattern[str]] = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
MARKER: Final[str] = "BOUNDARY-"
IMPORT_LINE: Final[re.Pattern[str]] = re.compile(
    r"^\s*(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$"
)
AUTO_IMPLICIT_FALSE: Final[re.Pattern[str]] = re.compile(
    r"^\s*set_option\s+autoImplicit\s+false\s*$", re.MULTILINE
)


class BoundaryAuditFailure(RuntimeError):  # noqa: N818
    """Raised when the separately elaborated Palomar boundaries differ."""


def repository_root() -> Path:
    """Return the repository root containing this script."""
    return Path(__file__).resolve().parent.parent


def string_list(config: object, key: str) -> list[str]:
    """Read and validate one string-list field from Comparator configuration."""
    if not isinstance(config, dict):
        raise BoundaryAuditFailure("comparator.json must contain a JSON object")
    value = config.get(key)
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise BoundaryAuditFailure(f"comparator.json {key} must be a list of strings")
    return value


def load_configuration(root: Path) -> tuple[str, str, list[str]]:
    """Return the two modules and every configured exported declaration."""
    path = root / "comparator.json"
    try:
        config: object = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BoundaryAuditFailure(f"cannot read valid {path.name}: {error}") from error
    if not isinstance(config, dict):
        raise BoundaryAuditFailure("comparator.json must contain a JSON object")
    challenge = config.get("challenge_module")
    solution = config.get("solution_module")
    if not isinstance(challenge, str) or LEAN_NAME.fullmatch(f"Root.{challenge}") is None:
        raise BoundaryAuditFailure("invalid Comparator challenge_module")
    if not isinstance(solution, str) or LEAN_NAME.fullmatch(f"Root.{solution}") is None:
        raise BoundaryAuditFailure("invalid Comparator solution_module")
    declarations = [
        *string_list(config, "theorem_names"),
        *string_list(config, "definition_names"),
    ]
    if not declarations:
        raise BoundaryAuditFailure("Comparator declaration list is empty")
    for declaration in declarations:
        if LEAN_NAME.fullmatch(declaration) is None:
            raise BoundaryAuditFailure(
                f"Comparator declaration must be a valid ASCII Lean name: {declaration!r}"
            )
    return challenge, solution, declarations


def module_source_path(root: Path, module: str) -> Path:
    """Resolve a root-relative Lean module to its source file."""
    path = root.joinpath(*module.split(".")).with_suffix(".lean")
    if not path.is_file():
        raise BoundaryAuditFailure(f"boundary module source does not exist: {path}")
    return path


def direct_imports(path: Path) -> tuple[str, ...]:
    """Return the direct Lean imports declared by one boundary source file."""
    try:
        source = path.read_text(encoding="utf-8")
    except OSError as error:
        raise BoundaryAuditFailure(f"cannot read {path}: {error}") from error
    return tuple(
        match.group(1)
        for line in source.splitlines()
        if (match := IMPORT_LINE.fullmatch(line)) is not None
    )


def require_boundary_source_policy(root: Path, challenge: str, solution: str) -> None:
    """Enforce the Mathlib-only Challenge and symmetric provider imports."""
    challenge_path = module_source_path(root, challenge)
    solution_path = module_source_path(root, solution)
    challenge_source = challenge_path.read_text(encoding="utf-8")
    solution_source = solution_path.read_text(encoding="utf-8")
    if AUTO_IMPLICIT_FALSE.search(challenge_source) is None:
        raise BoundaryAuditFailure(f"{challenge_path.name} must set autoImplicit false")
    if AUTO_IMPLICIT_FALSE.search(solution_source) is None:
        raise BoundaryAuditFailure(f"{solution_path.name} must set autoImplicit false")

    challenge_imports = direct_imports(challenge_path)
    non_mathlib = sorted(
        module
        for module in challenge_imports
        if module != "Mathlib" and not module.startswith("Mathlib.")
    )
    if non_mathlib:
        raise BoundaryAuditFailure(
            f"{challenge_path.name} has non-Mathlib direct imports: {', '.join(non_mathlib)}"
        )

    solution_imports = set(direct_imports(solution_path))
    missing = sorted(set(challenge_imports) - solution_imports)
    if missing:
        raise BoundaryAuditFailure(
            f"{solution_path.name} lacks direct Mathlib provider imports used by "
            f"{challenge_path.name}: {', '.join(missing)}"
        )


def probe_source(module: str, declarations: list[str]) -> str:
    """Generate a read-only command that exports raw elaborated type dependencies."""
    prefixes = sorted({f"{declaration.split('.', 1)[0]}." for declaration in declarations})
    internal_test = " || ".join(
        f"name.toString.startsWith {json.dumps(prefix)}" for prefix in prefixes
    )
    commands = "\n".join(f"#audit_boundary {name}" for name in declarations)
    return f"""import {module}
import Lean.Elab.Command

open Lean Elab Command

def boundaryInternal (root name : Name) : Bool :=
  name == root || {internal_test}

partial def auditTypeClosure
    (environment : Environment) (root : Name) (pending : List Name)
    (seen : NameSet := {{}}) : IO Unit := do
  match pending with
  | [] => pure ()
  | name :: rest =>
      if seen.contains name then
        auditTypeClosure environment root rest seen
      else
        match environment.find? name with
        | none => throw <| IO.userError s!"missing declaration dependency: {{name}}"
        | some info =>
            IO.println s!"BOUNDARY-TYPE|{{root}}|{{name}}|{{reprStr info.type}}"
            let mut dependencies := info.type.getUsedConstants.toList
            if boundaryInternal root name then
              match info with
              | .defnInfo value =>
                  IO.println s!"BOUNDARY-VALUE|{{root}}|{{name}}|{{reprStr value.value}}"
                  dependencies := value.value.getUsedConstants.toList ++ dependencies
              | _ => pure ()
            else
              dependencies := []
            auditTypeClosure environment root (dependencies ++ rest) (seen.insert name)

elab "#audit_boundary " name:ident : command => do
  let environment <- getEnv
  let root := name.getId
  match environment.find? root with
  | none => throwError "configured boundary declaration does not exist: {{root}}"
  | some _ =>
      liftIO <| IO.println s!"BOUNDARY-ROOT|{{root}}"
      liftIO <| auditTypeClosure environment root [root]

{commands}
"""


def run(command: list[str], root: Path) -> subprocess.CompletedProcess[str]:
    """Run a command and retain its output for a precise failure report."""
    return subprocess.run(command, cwd=root, check=False, capture_output=True, text=True)


def audit_module(lake: str, root: Path, module: str, declarations: list[str]) -> tuple[str, ...]:
    """Elaborate one boundary in isolation and return canonical audit records."""
    with tempfile.TemporaryDirectory(prefix="palomar-boundary-") as directory:
        probe = Path(directory) / f"{module.replace('.', '_')}_audit.lean"
        probe.write_text(probe_source(module, declarations), encoding="utf-8", newline="\n")
        result = run([lake, "env", "lean", str(probe)], root)
    if result.returncode != 0:
        detail = (result.stdout + result.stderr).strip()
        raise BoundaryAuditFailure(f"failed to audit {module}:\n{detail}")
    records = tuple(sorted(line for line in result.stdout.splitlines() if line.startswith(MARKER)))
    roots = {
        line.removeprefix("BOUNDARY-ROOT|") for line in records if line.startswith("BOUNDARY-ROOT|")
    }
    missing = sorted(set(declarations) - roots)
    if missing:
        raise BoundaryAuditFailure(f"{module} emitted no audit record for: {', '.join(missing)}")
    return records


def require_equal_exports(
    challenge_records: tuple[str, ...], solution_records: tuple[str, ...]
) -> None:
    """Reject any elaborated type or project-definition dependency mismatch."""
    if challenge_records == solution_records:
        return
    difference = "\n".join(
        difflib.unified_diff(
            challenge_records,
            solution_records,
            fromfile="Challenge elaboration",
            tofile="Solution elaboration",
            lineterm="",
        )
    )
    raise BoundaryAuditFailure("Palomar boundary exports differ:\n" + difference)


def main() -> int:
    """Build the narrow boundaries and compare every configured declaration."""
    root = repository_root()
    lake = shutil.which("lake")
    if lake is None:
        print("boundary audit failed: lake was not found on PATH", file=sys.stderr)
        return 1
    try:
        challenge, solution, declarations = load_configuration(root)
        require_boundary_source_policy(root, challenge, solution)
        build = run([lake, "build", challenge, solution], root)
        if build.returncode != 0:
            detail = (build.stdout + build.stderr).strip()
            raise BoundaryAuditFailure(f"boundary build failed:\n{detail}")
        challenge_records = audit_module(lake, root, challenge, declarations)
        solution_records = audit_module(lake, root, solution, declarations)
        require_equal_exports(challenge_records, solution_records)
    except BoundaryAuditFailure as error:
        print(f"boundary audit failed: {error}", file=sys.stderr)
        return 1
    print(f"boundary audit: {len(declarations)} declaration pair(s) match exactly")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
