# Bombieri-Vinogradov in Lean

[![CI](https://github.com/kimihiro64/bombieri-vinogradov/actions/workflows/ci.yml/badge.svg)](https://github.com/kimihiro64/bombieri-vinogradov/actions/workflows/ci.yml)

A source-faithful Lean 4 formalization of the Bombieri-Vinogradov theorem in the level-of-distribution form used by modern bounded-prime-gap arguments.

## Problem

**The Bombieri-Vinogradov theorem**

For every real theta < 1/2 and every real A >= 1, there exists a real c > 0 such that for every real x >= 3, the sum over 1 <= q <= floor(x^theta) of the maximum over reduced residue classes a modulo q of |pi(x; q, a) - pi(x)/phi(q)| is at most c*x/(log x)^A.

## Current status

This repository begins in research mode. `Challenge.lean` and `Solution.lean`
currently contain a clearly marked project-specific placeholder so that Lean,
documentation, and Comparator CI run while the proof remains open. It is not
the Bombieri-Vinogradov theorem. The exact target proposition already lives in
`BombieriVinogradov/Definitions/Statement.lean`; the Challenge/Solution surface
will be activated only after a proof of that proposition exists.

The release state is visible mechanically:

- while `formalization.yaml` contains the canonical `TEMPLATE:` sentinels, CI
  validates the starter surface but the repository is not submission-ready;
- after the real metadata and Challenge/Solution surface replace every
  sentinel, CI enforces the ordinary Palomar metadata contract.

## Repository map

- `Challenge.lean` — small human-auditable statement surface.
- `Solution.lean` — corresponding proved declarations.
- `BombieriVinogradov/` — proof development.
- `comparator.json` — exact Challenge/Solution declarations and axiom boundary.
- `formalization.yaml` — Palomar/community metadata, sources, fidelity, and
  review disclosure.
- `paper/` — public research paper source.
- `scripts/` — reproducible build, lint, experiment, certificate, and Palomar
  verification tools.
- `data/` — only reasonably sized data that is relevant and reproducible.

Local research context and AI working files are intentionally ignored and never
part of the public repository history.

## Build and checks

Install Git, Python 3.11+, Ruby, and `elan`, then run:

```text
python scripts/check.py --profile research
```

That checks the public-file boundary, Lean source policy, Python formatting,
lint, strict typing, tests, Palomar metadata mode, and the Lean build.

Before release, run:

```text
python scripts/check.py --profile release
./scripts/verify-comparator.sh
```

The Comparator command requires a supported Linux host with Git, Go, Ruby,
Rust/Cargo, Python, and Landrun. GitHub CI runs the pinned verifier stack.

## Paper

The paper should state the exact mathematical result, its significance, source
relationship, proof architecture, formalization trust boundary, computation or
certificate coverage, limitations, automation disclosure, and actual review
status. Every theorem presented as proved must map to a kernel-checked Lean
declaration.

## Palomar

Development may begin in this public repository so GitHub CI is available from
the outset. Submit only after the full release profile passes at a clean commit,
that exact 40-character SHA is pushed, and the current
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
has been reviewed. Use the
[Palomar submission form](https://submit.palomar-registry.org/) only for the
verified commit.

A successful Lean build, Comparator check, NanoDa replay, or automated review
does not by itself establish novelty, source fidelity, mathematical
significance, or independent expert review.

## Licence

This repository uses Apache-2.0. Cited mathematical sources, dependencies, and
supplied literature retain their own copyrights and licences.
