# Reciprocal-product deficit bounds with optimal global coefficients

This repository contains a complete Lean 4 development and a short research
note for quadratic deficit bounds for two- and three-point reciprocal
products. The author is **Mohith (MokiMeow)**.

The source compiles with Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Every theorem listed in the audit
has a complete proof. There are no `sorry`/`admit` placeholders, custom axioms,
`native_decide` shortcuts, or unsafe declarations in the published source.

This is a formal proof note, not a peer-reviewed paper. The exact fixed-weight
maximum used as background is known. No priority claim is made for the
distance estimates below; first-publication priority and journal novelty have
**not** been established.

## Main statements

For `0 < m < M`, positive weights `p,q`, and `x,y in [m,M]`, set

```text
Q(x,y) = (p*x + q*y) * (p/x + q/y)
Q*     = (p+q)^2 + p*q*(M-m)^2/(m*M)
```

Let `d2^2` be the squared Euclidean distance to
`{(m,M), (M,m)}`. The formal development proves

```text
Q* - Q(x,y) >= (p*q/(m*M)) * d2^2.
```

The coefficient `p*q/(m*M)` is optimal. It also proves the exact deficit
identity, equality classification, and the quantitative near-optimality
certificate `d2^2 <= m*M*epsilon/(p*q)`.

Optimality refers to the single coefficient valid on the entire interval.
This does not claim that squared distance gives the optimal local rate near
an endpoint maximizer; the near-optimality certificate can be loose there.

For the unweighted three-point product

```text
Q(x,y,z) = (x+y+z) * (1/x + 1/y + 1/z)
Q*       = 9 + 2*(M-m)^2/(m*M),
```

let `d3^2` be squared Euclidean distance to the six endpoint triples having
one or two coordinates equal to `M`. The development proves

```text
Q* - Q(x,y,z) >= (2/(m*M)) * d3^2,
```

and proves that `2/(m*M)` is the largest universally valid coefficient. The
proof covers every ordering of `(x,y,z)`. It uses six explicit polynomial
certificates with nonnegative coefficients; Lean checks each expansion and
its sign.

## What is established and what is not

The Lean kernel establishes the stated formal theorems relative to Lean's
logic and the imported mathlib definitions. The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`, the standard classical axioms
used by mathlib in this development. Targeted `leanchecker` replay verifies
the saved declarations again in the imported environment.

The following are deliberately separate from that result:

- The exact fixed-weight partition formula is established mathematics. It is
  formalized here as background, with sources cited below.
- The finite rational grid checks are debugging evidence, not proofs.
- Kernel replay is not verification by a second proof assistant.
- The larger-dimensional pattern mentioned in the note is experimental and
  is not a theorem in this release.
- A search that finds no matching paper cannot establish novelty. One relevant
  2026 paper could not be compared equation-by-equation from the accessible
  version, so priority remains unresolved.

## Source map

- `Kantorovich.lean` — 16 background theorems: endpoint rounding, the exact
  fixed-weight partition formula, the classical inequality, and attainment.
- `Kantorovich/Stability.lean` — 14 two-point stability theorems.
- `Kantorovich/ThreeCertificates.lean` — 6 polynomial certificates.
- `Kantorovich/ThreeStability.lean` — 18 three-point stability theorems.
- `Kantorovich/Examples.lean` — 3 exact rational examples.
- `Audit.lean` and `StabilityAudit.lean` — axiom reports for all 57 theorems.
- `reciprocal-stability.tex` and `paper/reciprocal-stability.pdf` — research
  note source and rendered PDF.
- `evidence/` — successful build, axiom, kernel-replay, sanity-check, and hash
  records for the tagged source.
- `RESEARCH.md` — development history, prior-art findings, and limitations.
- `independent-review.md` — scope and findings of a secondary draft critique;
  no human reviewer has assessed the work.

## Reproduce

Install the official Lean 4.34.0 release and make its `bin` directory available
on `PATH`. From `projects/reciprocal-stability` in the collection:

```text
lake exe cache get
lake build
lake build Kantorovich Kantorovich.Stability Kantorovich.ThreeCertificates Kantorovich.ThreeStability Kantorovich.Examples
lake env lean Audit.lean
lake env lean StabilityAudit.lean
lake env leanchecker -v Kantorovich Kantorovich.Stability Kantorovich.ThreeCertificates Kantorovich.ThreeStability Kantorovich.Examples
python sanity_checks.py
python stability_sanity.py
```

The dependency lock is committed. `lakefile.toml` pins mathlib directly to
`5ed2965256430c3649e86755f9576b54eca72435`; `lake-manifest.json` records all
transitive revisions. The release evidence records the actual tool versions,
commands, exit codes, source hashes, and output hashes.

## Literature checked

- Morris Newman, *Kantorovich's inequality*, Journal of Research of the
  National Bureau of Standards B 64B (1960), 33–34.
  [NIST PDF](https://nvlpubs.nist.gov/nistpubs/jres/64B/jresv64Bn1p33_A1b.pdf)
- Constantin P. Niculescu and Lars-Erik Persson, *Convex Functions and Their
  Applications*, manuscript dated 16 September 2004, Section 1.4, Exercise 1,
  p. 32. [Manuscript PDF](https://carmamaths.org/resources/jon/Preprints/Books/CUP/CUPold/np-convex.pdf)
- A. Lupaş, *A remark on the Schweitzer and Kantorovich inequalities* (1972),
  13–15. [Source PDF](https://ictp.acad.ro/wp-content/uploads/2025/11/1972-Lupas-Publikacije-A-remark-on-the-Schweitzer-and-Kantorovich-inequalities.pdf)
- Alqahtani and M. Z. Sarikaya, *Refined Weighted Schweitzer-Type Inequalities
  With Applications to Statistical Moments*, Journal of Mathematics (2026),
  article 4822611. [DOI](https://doi.org/10.1155/jom/4822611)

The last paper is relevant neighboring work. Its accessible HTML did not
include the equations needed for a definitive overlap check, and the full text
was not retrieved. This repository therefore makes no priority claim.

## License

The original source and note in this repository are released under the MIT
License. Mathlib and other dependencies retain their own licenses.
