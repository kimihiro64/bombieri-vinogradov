# Licensing scope

The single repository-level licence for Bombieri-Vinogradov in Lean is the
[Apache License 2.0](LICENSE), as recorded by `project.license` in
`formalization.yaml`. Except where a file says otherwise, Apache-2.0 applies
to the copyrightable interests that project contributors are authorized to
license in original repository material, including Lean source, scripts,
configuration, project documentation, and project-authored data arrangements.

## Research paper

The original expression in `paper/research-paper.tex` and the PDF built from
it is available, at the recipient's choice, under either:

- Apache License 2.0; or
- [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/)
  (`CC-BY-4.0`).

The paper carries this notice in both its source and rendered PDF. This
additional option does not replace or make ambiguous the repository's
Apache-2.0 default.

## Mathematics, sources, and dependencies

Licensing and scholarly provenance are separate:

- This repository does not claim ownership of mathematical statements, facts,
  methods, or results. Attribution and the relationship between cited sources
  and Lean declarations are recorded in `formalization.yaml` and the research
  paper.
- Cited papers and supplied literature retain their own copyrights and terms
  of access. The repository licence does not relicense them.
- Git dependencies named in `lake-manifest.json` and the Lean toolchain retain
  their own licences and copyright notices.
- A file incorporating third-party copyrightable material remains subject to
  the third party's notice and licence as well as any licence applying to
  project-authored modifications.

## Generated distributions

The Linux Lean-build release archive contains compiled project build outputs
and a copy of this licensing information. It does not include checked-out
dependency source trees under `.lake/packages`.

The API-documentation archive is an aggregate: doc-gen4 emits pages for
Bombieri-Vinogradov in Lean and transitive imports so declaration links work
offline. CI therefore adds a `licensing/` directory containing this project
notice, the root Apache-2.0 text, Lean toolchain notices, and top-level licence
or notice files from every pinned package represented in the documentation.
Nothing in that archive changes the terms applying to third-party material.

## Contributions

Unless explicitly agreed and marked otherwise, contributions are accepted
under Apache-2.0. Contributors must preserve applicable third-party notices
and submit only material they are authorized to license.
