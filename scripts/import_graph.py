"""Check Lean/Python file size, layering, cycles, and dependency blast radius."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Final, cast

ROOT = Path(__file__).resolve().parent.parent
if __package__ in {None, ""}:
    sys.path.insert(0, str(ROOT))

from scripts.check import lean_imports, strip_lean_comments  # noqa: E402

LEAN_RECOMMENDED_LINES: Final[int] = 500
LEAN_MAX_LINES: Final[int] = 900
PYTHON_RECOMMENDED_LINES: Final[int] = 300
PYTHON_MAX_LINES: Final[int] = 450
MAX_DIRECT_OWNED_IMPORTS: Final[int] = 12
PROOF_IMPACT_WARNING: Final[int] = 12
LAYERS: Final[dict[str, int]] = {
    "Definitions": 0,
    "Helpers": 1,
    "Proof": 2,
    "Assembly": 3,
}


class ArchitectureFailure(RuntimeError):  # noqa: N818
    """Raised when module architecture violates a hard invariant."""


def repository_root() -> Path:
    """Return the public repository root."""
    return ROOT


def library_namespace(root: Path) -> str:
    """Find the one project library root module."""
    candidates = sorted(
        path.stem
        for path in root.glob("*.lean")
        if path.name not in {"Challenge.lean", "Solution.lean"} and (root / path.stem).is_dir()
    )
    if len(candidates) != 1:
        raise ArchitectureFailure(
            f"expected one project library root module, found {', '.join(candidates) or 'none'}"
        )
    return candidates[0]


def module_map(root: Path, namespace: str) -> dict[str, Path]:
    """Map owned Lean module names to source paths."""
    result = {
        "Challenge": root / "Challenge.lean",
        "Solution": root / "Solution.lean",
        namespace: root / f"{namespace}.lean",
    }
    for path in sorted((root / namespace).rglob("*.lean")):
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        result[module] = path
    return result


def owned_graph(root: Path, namespace: str) -> tuple[dict[str, Path], dict[str, set[str]]]:
    """Return owned paths and direct owned imports."""
    modules = module_map(root, namespace)
    graph: dict[str, set[str]] = {}
    for module, path in modules.items():
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        graph[module] = {name for name in lean_imports(code) if name in modules}
    return modules, graph


def detect_cycles(graph: Mapping[str, set[str]]) -> list[list[str]]:
    """Return dependency cycles in a directed graph."""
    state: dict[str, int] = {}
    stack: list[str] = []
    cycles: list[list[str]] = []

    def visit(node: str) -> None:
        state[node] = 1
        stack.append(node)
        for dependency in sorted(graph.get(node, set())):
            if state.get(dependency, 0) == 0:
                visit(dependency)
            elif state.get(dependency) == 1:
                start = stack.index(dependency)
                cycles.append([*stack[start:], dependency])
        stack.pop()
        state[node] = 2

    for node in sorted(graph):
        if state.get(node, 0) == 0:
            visit(node)
    return cycles


def module_layer(module: str, namespace: str) -> int | None:
    """Return the architectural layer for a project module."""
    if module == namespace:
        return 4
    prefix = f"{namespace}."
    if not module.startswith(prefix):
        return None
    component = module[len(prefix) :].split(".", 1)[0]
    return LAYERS.get(component)


def proof_branch(module: str, namespace: str) -> str | None:
    """Return the first proof-branch component, if present."""
    prefix = f"{namespace}.Proof."
    if not module.startswith(prefix):
        return None
    remainder = module[len(prefix) :]
    return remainder.split(".", 1)[0] if remainder else None


def transitive_dependents(graph: Mapping[str, set[str]]) -> dict[str, set[str]]:
    """Return all modules transitively invalidated by changing each module."""
    reverse: dict[str, set[str]] = defaultdict(set)
    for importer, dependencies in graph.items():
        for dependency in dependencies:
            reverse[dependency].add(importer)
    result: dict[str, set[str]] = {}
    for module in graph:
        seen: set[str] = set()
        pending = list(reverse.get(module, set()))
        while pending:
            dependent = pending.pop()
            if dependent in seen:
                continue
            seen.add(dependent)
            pending.extend(reverse.get(dependent, set()))
        result[module] = seen
    return result


def line_count(path: Path) -> int:
    """Count text lines deterministically."""
    return len(path.read_text(encoding="utf-8").splitlines())


def audit_architecture(root: Path) -> dict[str, object]:
    """Audit hard architecture rules and return a dependency report."""
    namespace = library_namespace(root)
    modules, graph = owned_graph(root, namespace)
    failures: list[str] = []
    warnings: list[str] = []

    cycles = detect_cycles(graph)
    failures.extend("dependency cycle: " + " -> ".join(cycle) for cycle in cycles)
    for importer, dependencies in graph.items():
        if len(dependencies) > MAX_DIRECT_OWNED_IMPORTS:
            message = (
                f"{importer}: {len(dependencies)} direct owned imports exceeds "
                f"{MAX_DIRECT_OWNED_IMPORTS}"
            )
            failures.append(message)
        importer_layer = module_layer(importer, namespace)
        for dependency in sorted(dependencies):
            dependency_layer = module_layer(dependency, namespace)
            if (
                importer_layer is not None
                and dependency_layer is not None
                and importer_layer < dependency_layer
            ):
                failures.append(f"layer inversion: {importer} imports {dependency}")
            importer_branch = proof_branch(importer, namespace)
            dependency_branch = proof_branch(dependency, namespace)
            if (
                importer_branch is not None
                and dependency_branch is not None
                and importer_branch != dependency_branch
            ):
                failures.append(f"sibling proof branch import: {importer} imports {dependency}")

    for module, path in modules.items():
        lines = line_count(path)
        if lines > LEAN_MAX_LINES:
            failures.append(f"{module}: {lines} Lean lines exceeds hard limit {LEAN_MAX_LINES}")
        elif lines > LEAN_RECOMMENDED_LINES:
            warnings.append(f"{module}: {lines} Lean lines; split before {LEAN_MAX_LINES}")
    for path in sorted((root / "scripts").rglob("*.py")):
        lines = line_count(path)
        relative = path.relative_to(root).as_posix()
        if lines > PYTHON_MAX_LINES:
            failures.append(
                f"{relative}: {lines} Python lines exceeds hard limit {PYTHON_MAX_LINES}"
            )
        elif lines > PYTHON_RECOMMENDED_LINES:
            warnings.append(f"{relative}: {lines} Python lines; split before {PYTHON_MAX_LINES}")

    impact = transitive_dependents(graph)
    for module, dependents in impact.items():
        if proof_branch(module, namespace) is not None and len(dependents) > PROOF_IMPACT_WARNING:
            warnings.append(
                f"{module}: volatile proof module has {len(dependents)} transitive dependents"
            )
    if failures:
        raise ArchitectureFailure("architecture audit failed:\n" + "\n".join(failures))
    return {
        "namespace": namespace,
        "modules": len(modules),
        "edges": sum(len(dependencies) for dependencies in graph.values()),
        "warnings": warnings,
        "transitive_dependents": {
            module: len(dependents) for module, dependents in sorted(impact.items())
        },
    }


def parse_arguments(arguments: Sequence[str] | None = None) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(arguments)


def main(arguments: Sequence[str] | None = None) -> int:
    """Audit and print the dependency report."""
    options = parse_arguments(arguments)
    try:
        report = audit_architecture(repository_root())
    except (ArchitectureFailure, OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    if options.json:
        print(json.dumps(report, indent=2, ensure_ascii=True))
    else:
        print(f"architecture: clean ({report['modules']} modules, {report['edges']} owned edges)")
        for warning in cast(list[str], report["warnings"]):
            print(f"warning: {warning}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
