# Draft statement critique

A secondary read-only critique inspected the mathematical statements and
proof structure. No human reviewer has assessed this work, and no external
peer review, maintainer acceptance, or journal decision has occurred. These
notes are supplementary commentary; the formal proofs and their verification
record establish the mathematical claims.

## Background fixed-weight theorem

No critical or important mathematical defect was found in the chord identity,
nonnegative-offset induction, quantifier order `exists S, forall x`, endpoint
partition identity, strictness result, or equal-partition attainment theorem.
Empty sets, zero weights, and equal interval endpoints were explicitly checked.
The exact fixed-weight formula was found in existing literature and is not a
new result.

## Two-point stability theorem

No correctness defect was found in the deficit identity, sorted scalar
certificate, symmetry reduction, distance definition, equality classification,
or sharpness witness. The coefficient `p*q/(m*M)` is supported by a valid
global inequality and a witness that rules out every larger coefficient.
The result is elementary enough that the review does not treat it alone as
evidence of journal-level novelty.

## Three-point stability theorem

No substantive correctness issue was found. The review checked that:

- the three lower-half cones cover the sorted lower region, including their
  boundaries;
- the reflected cover maps the upper region to the lower region, while the
  proof correctly uses separate upper polynomial certificates;
- the product and the explicit six-point distance are invariant under the
  transpositions used to cover all six coordinate orderings;
- the all-lower-endpoint witness proves optimality of `2/(m*M)`; and
- the formal distance is exactly squared Euclidean distance to the six stated
  endpoint triples with one or two upper-endpoint coordinates.

The review also identified an important distinction preserved in the note:
`(m,(m+M)/2,M)` and its permutations can attain equality in the stability
bound at positive distance, but they are not objective maximizers.

## Limits of the review

The reviewer did not independently run the compiler or kernel replay; those
checks are recorded separately in `evidence/`. The reviewer did not establish
first-publication priority. A focused literature search did not find the exact
three-variable distance estimate, but a relevant 2026 Schweitzer-type
refinement could not be compared from the accessible equations. The result is
therefore described as a candidate refinement with a complete formal proof,
not as a certified solution of a previously open problem.
