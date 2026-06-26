# Mathlib contribution candidates

General-purpose lemmas developed for the Leshno (1993) universal approximation
formalization that are candidates for upstreaming to Mathlib. Each is stated in a
project-neutral namespace with general typeclasses (no `UniversalApproximation`
dependency) and tagged `-- TODO(mathlib)` in source.

Status legend: `scaffolded` (statement elaborates, proof is `sorry`) · `proved`
(proof complete in-project) · `PR #N` (upstream pull request opened).

| Lemma | File | One-line statement | Intended Mathlib location | Status |
|---|---|---|---|---|
| `iteratedDeriv_eq_zero_imp_poly` | `LeanPlayground/ForMathlib/IteratedDerivPolynomial.lean` | If `iteratedDeriv n f = 0` everywhere (with `ContDiff ℝ n f`), then `f` equals a `Polynomial ℝ` of `natDegree < n`. | `Mathlib/Analysis/Calculus/IteratedDeriv/` | scaffolded |
| `ridgePow_span` | `LeanPlayground/ForMathlib/RidgePowersSpan.lean` | The functions `x ↦ (∑ i, a i * x i) ^ k` (over `a : Fin n → ℝ`) span the image under `MvPolynomial.evalₗ ℝ (Fin n)` of `MvPolynomial.homogeneousSubmodule (Fin n) ℝ k`. | `Mathlib/LinearAlgebra/Polynomial` / `Mathlib/RingTheory/MvPolynomial` | scaffolded |
| _(conditional)_ convolution Riemann-sum approximation | `LeanPlayground/ForMathlib/` (Task 5, TBD) | A continuous function is uniformly approximable on compacts by Riemann sums of its convolution against a mollifier (Lemma A core). | `Mathlib/Analysis/Convolution` / `Mathlib/MeasureTheory/Integral` | pending (Task 5) |

## Mathlib-absence findings (toolchain pin `v4.32.0-rc1`)

Searches run with `lean_leansearch` / `lean_loogle` on 2026-06-26.

### `iteratedDeriv_eq_zero_imp_poly`
- `lean_loogle "iteratedDeriv ?n ?f = 0"` returned no results.
- `lean_leansearch "function with vanishing iterated derivative is a polynomial"`
  returned only related/forward-direction facts, none giving the converse we need:
  - `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` (analytic-order
    characterisation: `↑n ≤ analyticOrderAt f z₀ ↔ ∀ i < n, iteratedDeriv i f z₀ = 0`);
  - `Polynomial.iterate_derivative_eq_zero_of_degree_lt` (polynomial ⇒ derivative
    zero — the forward direction);
  - `Polynomial.fwdDiff_iter_degree_add_one_eq_zero` (forward-difference analogue).
- Conclusion: the statement "vanishing `n`-th iterated derivative ⇒ polynomial of
  degree `< n`" is **not** present. Wrapper retained; proof to follow in Task 4.

### `ridgePow_span`
- `lean_leansearch "powers of linear functionals span homogeneous polynomials polarization"`
  returned only adjacent material, none stating the polarization span we need:
  - `Ideal.mem_span_pow_iff_exists_isHomogeneous` (membership in the `n`-th power of
    an *ideal* span, not the `Submodule`-span of powers of linear forms as functions);
  - `MvPolynomial.homogeneousSubmodule_one_pow`
    (`homogeneousSubmodule σ R 1 ^ n = homogeneousSubmodule σ R n` — an algebra/ideal
    identity, not the function-space span);
  - `MvPolynomial.homogeneousSubmodule`, `homogeneousSubmodule_one_eq_span_X`,
    `MvPolynomial.evalₗ` are the existing building blocks reused to phrase the RHS.
- Conclusion: the "powers of linear forms span the homogeneous polynomial functions"
  statement is **not** present. Wrapper retained; proof to follow in Task 6.

## `ridgePow_span` right-hand-side choice

The left-hand side is a `Submodule ℝ ((Fin n → ℝ) → ℝ)` (span of the *functions*
`x ↦ (∑ i, a i * x i) ^ k`), so the RHS must live in the same function space. We take
it to be `Submodule.map (MvPolynomial.evalₗ ℝ (Fin n)) (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)`:
the image, under the evaluation-as-linear-map `evalₗ`, of Mathlib's canonical submodule
of homogeneous degree-`k` polynomials. This names "homogeneous degree-`k` polynomial
functions" via existing Mathlib API (`homogeneousSubmodule` + `evalₗ`) rather than
reinventing a monomial span, keeps both sides in `(Fin n → ℝ) → ℝ`, and makes the
`⊆` inclusion definitionally on track (each generator is the evaluation of the
homogeneous polynomial `(∑ i, C (a i) * X i) ^ k`). The statement elaborates with only
the `sorry`-proof warning.
