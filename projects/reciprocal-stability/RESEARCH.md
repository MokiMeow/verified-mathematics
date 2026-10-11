# Finite weighted Kantorovich inequality: research record

## Intended result

For an arbitrary finite index set, nonnegative fixed weights `w_i`, and real
values `0 < m <= x_i <= M`, verify that the maximum of

`(sum w_i*x_i) * (sum w_i/x_i)`

is attained with every `x_i` equal to `m` or `M`. For an endpoint partition
with lower-endpoint weight `u` and upper-endpoint weight `v`, prove the exact
identity

`4*m*M*objective = (m+M)^2*(u+v)^2 - (M-m)^2*(u-v)^2`.

Consequently, the optimal bound for the fixed weights is determined by the
smallest squared imbalance among their finite partitions. Verify the usual
Kantorovich bound as a corollary and explicit cases where the fixed-weight
bound is strictly smaller. Include zero weights, an empty index set, and
`m = M`; do not silently assume normalization or strict separation.

## Proof approach

With all other coordinates fixed and nonnegative sums `A,B`, the varying
coordinate contributes `(A+p*t)*(B+p/t)`. For `m < M`, the chord value
minus that objective is `p*A*(M-t)*(t-m)/(m*M*t)`, which is nonnegative.
The case `m = M` is handled separately. Thus some endpoint is at least as
good. Induct over the finite index set,
retaining nonnegative offsets, to round every coordinate to an endpoint.
Then evaluate the product algebraically and minimize the finite partition
imbalance. Divisions used in the inequalities and chord-gap argument have
proved positive denominators. The endpoint-evaluation identity is purely
algebraic and also permits zero endpoints under Lean's total division;
the final inequality and sharpness results require `0 < m <= M`.

## Scope and novelty

This is a formalization of known mathematics, not a solution of an open
conjecture. Publication suitability and first-formalization priority are
unestablished. Search absence does not establish novelty. A research note
will distinguish the literature result, our proof artifact, and unresolved
extensions. No journal, preprint, repository, or public claim is authorized
merely by producing this private artifact.

## Candidate screening

- Elementary Erdos-Straus congruence families: existing Lean proofs found;
  do not duplicate them or claim to solve the full conjecture.
- Classical Cerny automata bounds and exact reset thresholds: recent Lean
  formalizations found; general conjecture is far beyond this small probe.
- Motzkin-Straus theorem: existing related Lean development found.
- Quadratic Jury stability test: existing complete Lean artifact found.
- Fixed-weight sharp Kantorovich inequality: promising bounded target;
  check the pinned library and primary literature before making any
  first-formalization or publication claim.

## References to inspect

- Morris Newman, *Kantorovich's inequality*, Journal of Research of the
  National Bureau of Standards 64B (1960), pp. 33-34:
  https://nvlpubs.nist.gov/nistpubs/jres/64B/jresv64Bn1p33_A1b.pdf
- W. Greub and W. Rheinboldt, *On a generalization of an inequality of
  L. V. Kantorovich*, Proceedings of the AMS 10 (1959), pp. 407-415:
  https://doi.org/10.1090/S0002-9939-1959-0105028-3

The downloaded original identifies Newman as author (corrected after
reading the PDF). The bound belongs to established literature.

## Reproducibility plan

Lean 4.34.0, mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Local project only. Mathlib is an unmodified dependency; its contribution
policy requires disclosure and bans generated public comments, so no
mathlib PR or public discussion will be made under the user's current
contribution rules. Verify every final theorem with Lean and print axiom
dependencies. No `sorry`, custom axioms, `native_decide`, or imported
assumptions that assert the target theorem. Numerical checks are sanity
checks, not the proof.

## Verified outcome

The complete Lean development compiles and its own declarations pass
targeted kernel replay. Final printed axiom dependencies are only
`propext`, `Classical.choice`, and `Quot.sound`. Independent mathematical
critique found no substantive defects after final additions. No human reviewer
has assessed this work. The exact
example with weights `(1,2)` on `[1,4]` has maximum `27/2`, below the classical `225/16`.
Publication novelty remains unestablished; this is a checked proof of
known finite weighted mathematics.

## Later prior-art check

An existing Lean proof of Newman's normalized scalar inequality was
located at https://joshua.plus/lean-old-papers/downloads/Kantorovich.lean.
Its 5 theorems cover the classical inequality and a half-mass equality
example, not the fixed-weight optimal partition theorem or general
attainment criterion. This was read after our proof was developed.
The classical corollary overlaps prior formal work; no priority is
claimed for it. This discovery is recorded instead of omitted.

## Sharp stability extension

The subsequent investigation isolated a quantitative question not answered by
the exact maximum alone: how does the objective deficit control Euclidean
distance to the endpoint maximizing set?

For two weighted coordinates, the completed proof gives the globally optimal
coefficient `p*q/(m*M)`. For three unweighted coordinates, it gives the
globally optimal coefficient `2/(m*M)` for distance to the six endpoint
triples with one or two coordinates equal to `M`. The three-coordinate argument covers the ordered domain by
three lower-half cones and their reflected upper-half cones. Separate Lean
lemmas verify the six polynomial expansions; reflection is used only to move
the domain and is not assumed to preserve the reciprocal objective.

The final formal inventory is 57 theorems: 16 background results, 14
two-point stability results, 6 certificate lemmas, 18 three-point stability
results, and 3 exact examples. A stability equality need not be an objective
maximizer: `(m,(m+M)/2,M)` is the concrete three-point warning case recorded
in the note.

A secondary read-only critique found no defect in the inequality, cone cover,
permutation reduction, metric definition, or optimal-coefficient witness.
Compilation, axiom printing, targeted kernel replay, and exact rational grid
checks are separately recorded. The review is not peer review and does not
establish publication priority.

## Remaining novelty limitation

The fixed-weight optimum and equal-weight parity correction have explicit
prior art. A focused search did not locate the exact two- or three-point
Euclidean-distance estimates, but absence of a match is not proof of novelty.
The 2026 article *Refined Weighted Schweitzer-Type Inequalities With
Applications to Statistical Moments* is relevant neighboring work. Its
accessible HTML omitted the equations needed for a definitive comparison and
the full remainder was not retrieved. The public release therefore presents a
verified research note and candidate refinement, not a claim that an open
problem has been solved or that a journal will accept it.
