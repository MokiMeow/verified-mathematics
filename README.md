# Verified mathematics

Formal mathematical developments by **Mohith (MokiMeow)**, collected in one
repository. Each completed project has its own proofs, statement guide,
dependency pins, verification evidence, and research note.

| Project | What is proved | Evidence | Status |
| --- | --- | --- | --- |
| [Reciprocal-product stability](projects/reciprocal-stability/README.md) | Two- and three-point quadratic deficit bounds with globally optimal coefficients; fixed-weight endpoint background | 57 audited Lean theorems, five modules replayed, recorded commands and SHA256 hashes | Locally verified on Windows and Linux; formal proof note, not peer reviewed; novelty unresolved |

The source and evidence are in
[`projects/reciprocal-stability/`](projects/reciprocal-stability/).
See its [research note](projects/reciprocal-stability/paper/reciprocal-stability.pdf),
[verification record](projects/reciprocal-stability/evidence/verification.json),
and [limitations](projects/reciprocal-stability/RESEARCH.md).

## Reproduce a project

Install the Lean version specified by the project's `lean-toolchain`, then:

```text
cd projects/reciprocal-stability
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean StabilityAudit.lean
lake env lean -DwarningAsError=true SequentialReplay.lean
python sanity_checks.py
python stability_sanity.py
```

The project also includes `verify.ps1` to record fresh source checks and
evidence. Paths in its evidence are relative to the project directory.
The original `v1.0.0` release retains the original layout and original bytes;
moving them into this collection does not change the formal statements.

## Scope

Formal checking establishes the encoded statements relative to the listed
logic, axioms, and dependencies. It does not certify priority, journal
acceptance, the fidelity of a physical model, or numerical software behavior.
Exploratory or incomplete work is kept out of the completed-project table.
New research results await author review before publication.

The original material is MIT licensed. Dependencies retain their own licenses.
