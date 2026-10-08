# Formalization

This directory contains all project proofs for the paper and the six-presentation
refinement mentioned in its closing remark. It requires only the pinned Lean and
Mathlib software dependencies, not another research repository.

## Build and verify

Install Lean using `elan`. From this directory, run:

```bash
lake exe cache get
bash verification/check.sh
```

`lean-toolchain` and `lake-manifest.json` pin the software versions. The cache
command downloads compiled dependencies; they can instead be built from source.
The check command builds the proof and audits every project declaration for
additional axioms. For an additional kernel replay, use:

```bash
bash verification/check.sh --replay
```

The generated `.lake/` directory is a local cache and is not publication content.

## Theorem locations

All declarations below are in namespace `Lambert`.

| Declaration | Source |
|---|---|
| `lambertValue_no_relation_of_numberField_height` | [Main theorem](Lambert/Results/MainTheorem.lean) |
| `lambertValue_no_relation_of_mahler_margin` | [Main theorem](Lambert/Results/MainTheorem.lean) |
| `lambertValue_relative_degree_gt_of_mahler_margin` | [Main theorem](Lambert/Results/MainTheorem.lean) |
| `lambertValue_no_polynomial_relation_of_rational_margin` | [Rational bases](Lambert/Results/RationalBases.lean) |
| `lambertValue_no_polynomial_relation_of_rational_region` | [Rational bases](Lambert/Results/RationalBases.lean) |
| `lambertValue_irrational_of_rational_region` | [Rational bases](Lambert/Results/RationalBases.lean) |
| `lambertValue_irrational_of_log_ratio_lt_5728` | [Rational bases](Lambert/Results/RationalBases.lean) |
| `lambertValue_no_quadratic_relation_of_conjugates` | [Conjugate criteria](Lambert/Results/AlgebraicBaseCorollaries.lean) |
| `lambertValue_quadratic_coefficients_eq_zero_of_conjugates` | [Conjugate criteria](Lambert/Results/AlgebraicBaseCorollaries.lean) |
| `lambertValue_no_relation_of_radical_degree_margin` | [Radical bases](Lambert/Results/RadicalBase.lean) |
| `lambertValue_no_relation_of_radical_margin` | [Radical bases](Lambert/Results/RadicalBase.lean) |
| `lambertValue_sqrt_not_mem` | [Radical bases](Lambert/Results/RadicalBase.lean) |
| `lambertValue_integer_no_quadratic_relation` | [Integer bases](Lambert/Results/DegreeExclusion.lean) |
| `erdosBorwein_no_quadratic_relation` | [Integer bases](Lambert/Results/DegreeExclusion.lean) |
| `lambertValue_algebraic_degree_gt_of_refinement_margin` | [Rational refinement](Lambert/Refinement/RationalRefinement.lean) |
| `lambertValue_no_polynomial_relation_of_refinement_margin` | [Rational refinement](Lambert/Refinement/RationalRefinement.lean) |
| `lambertValue_no_polynomial_relation_of_refinement_region` | [Rational refinement](Lambert/Refinement/RationalRefinement.lean) |
| `lambertValue_no_polynomial_relation_of_certified_region` | [Rational refinement](Lambert/Refinement/RationalRefinement.lean) |
| `lambertValue_irrational_of_refinement_region` | [Refined irrationality](Lambert/Refinement/Irrationality.lean) |
| `lambertValue_irrational_of_certified_region` | [Refined irrationality](Lambert/Refinement/Irrationality.lean) |

`Lambert/Basic.lean` defines the series and proves convergence.
`Lambert/Main.lean` imports the main theorem and its stated corollaries.
`Lambert/Refinement.lean` imports the refined rational criterion.
`Lambert.lean` imports both. Supporting proofs are grouped under `Analysis`,
`Arithmetic`, and `Determinants`; the refinement has its own subdirectory.

## Refinement certificate

Lean proves the validity of the 400 rational cells in
`Lambert/Refinement/ProfileData.lean`. Python is not required to build
or verify the proof. The optional generator reproduces that file exactly:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 certificate/lambert_profile.py --check
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s certificate/tests
```

These commands use only Python's standard library. The tests compare the
generator against direct integer-profile calculations.
