# Bombieri-Vinogradov in Lean

[![CI](https://github.com/kimihiro64/bombieri-vinogradov/actions/workflows/ci.yml/badge.svg)](https://github.com/kimihiro64/bombieri-vinogradov/actions/workflows/ci.yml)

A Lean 4 formalization of the Bombieri-Vinogradov theorem in the
level-of-distribution form used by modern bounded-prime-gap arguments.

## Theorem

For every real `theta < 1/2` and every real `A >= 1`, there is a real
`c > 0` such that for every real `x >= 3`,

```text
sum_{1 <= q <= floor(x^theta)}
  max_{a in (ZMod q)^x} |pi(x; q, a) - pi(x)/phi(q)|
    <= c*x/(log x)^A.
```

The modulus cutoff is inclusive, the maximum is over reduced residue classes,
and the theorem does not claim the endpoint `theta = 1/2`.

## Status

The exact theorem is proved. `Challenge.lean` contains the deliberate Palomar
statement hole and imports only Mathlib. `Solution.lean` exports the identical
declaration type and closes it with
`BombieriVinogradov.PrimeCountingConversion.weighted_to_prime_counting`.

The formal proof includes:

- an additive large sieve and primitive character reduction, with explicit
  character-large-sieve coefficient `36`;
- a finite Vaughan identity whose sign and cutoff convention were checked
  against the coefficient algebra;
- a real-endpoint Vaughan mean-value theorem with explicit coefficient
  `200000`;
- a character-form Siegel-Walfisz theorem with one absolute exponential rate;
- a globally centered maximal von Mangoldt Bombieri-Vinogradov estimate;
- prime-power removal and equality-safe reciprocal-log Abel summation;
- logarithmic absorption of the averaged prime-power error for every
  `theta < 1/2`, including bounded real endpoints.

The project proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
No numerical certificate or stronger prime number theorem is used to close the
headline result.

## Repository map

- `Challenge.lean` - Mathlib-only advertised statement.
- `Solution.lean` - proved declaration with the same exported type.
- `BombieriVinogradov/Definitions/` - stable mathematical interfaces.
- `BombieriVinogradov/Helpers/` - reusable analytic and algebraic lemmas.
- `BombieriVinogradov/Proof/` - independent proof branches.
- `BombieriVinogradov/Assembly/` - low-complexity theorem composition.
- `comparator.json` - exact declaration pairs and permitted axiom boundary.
- `formalization.yaml` - Palomar metadata, source fidelity, and review status.
- `paper/research-paper.tex` - public mathematical account.
- `scripts/` - reproducible checks, documentation, and release packaging.

Local research records, AI instructions, literature copies, and disposable
proof probes are ignored and are not part of the public history.

## Build and verification

Install Git, Python 3.11+, Ruby, and `elan`, then run:

```text
python scripts/check.py --profile research
```

Before release, run:

```text
python scripts/check.py --profile release
./scripts/verify-comparator.sh
```

The verifier uses the reviewed Lean 4.33.1-compatible `lean4export` source,
the pinned Comparator, NanoDa replay, and the Lean default kernel. The boundary
audit checks elaborated declaration types and dependencies, not only source
text. Every generated shell script is tracked with executable mode.

## Releases

`RELEASE_VERSION` contains the semantic version for the next release. A
successful release workflow is gated on the complete Lean build, metadata and
provenance checks, paper, offline documentation, Comparator, NanoDa, the Lean
default kernel, and source-only licensing smoke tests. It publishes exactly
the paper PDF, a Linux `.lake/build` archive, and an offline documentation ZIP.

## Paper and licensing

The paper gives the source history, proof architecture, declaration ledger,
trust boundary, divergences, and review status. Its project-authored TeX source
and rendered PDF are available under `Apache-2.0 OR CC-BY-4.0`. The repository
default remains Apache-2.0. See [LICENSING.md](LICENSING.md) for the scope and
third-party exclusions.

## Palomar

Submit only a clean, pushed commit whose release profile and pinned replays all
pass, then use the current [Palomar submission form](https://submit.palomar-registry.org/).
The submission metadata does not claim independent expert review.
