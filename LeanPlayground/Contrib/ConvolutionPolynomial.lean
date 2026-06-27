import Mathlib

/-! # Convolution of polynomials with test functions, and commutativity for the `mul` pairing.
Intended Mathlib home: `Mathlib/Analysis/Convolution` (confirm with maintainers). -/

namespace ConvolutionPolynomial

open MeasureTheory

open scoped ContDiff

/-- Commutativity of the real convolution taken against scalar multiplication `mul ℝ ℝ`. -/
theorem convolution_comm_mul (f g : ℝ → ℝ) :
    convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume
      = convolution g f (ContinuousLinearMap.mul ℝ ℝ) volume := by
  nth_rewrite 1 [← ContinuousLinearMap.flip_mul]
  rw [convolution_flip]

/-- `φ ⋆ σ` exists pointwise when `φ` is continuous with compact support and `σ` is locally
integrable. -/
theorem convolutionExists_left_mul {φ σ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hσ : LocallyIntegrable σ volume) :
    ConvolutionExists φ σ (ContinuousLinearMap.mul ℝ ℝ) volume :=
  hφc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hφ hσ

/-- `σ ⋆ ψ` exists pointwise when `ψ` is continuous with compact support and `σ` is locally
integrable. -/
theorem convolutionExists_right_mul {σ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ConvolutionExists σ ψ (ContinuousLinearMap.mul ℝ ℝ) volume :=
  hψc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hσ hψ

/-- Convolving the monomial `x ↦ xⁿ` with a continuous compactly-supported `ψ` gives a polynomial
of degree `≤ n` whose `n`-th coefficient is the `0`-th moment `∫ ψ`. -/
theorem monomial_conv_isPoly {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (n : ℕ) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, (x - y) ^ n * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree ≤ n ∧ q.coeff n = ∫ y, ψ y := by
  -- integrability of `(continuous g) * ψ`, used for each summand of `sub_pow`
  have hint : ∀ (g : ℝ → ℝ), Continuous g → Integrable (fun y => g y * ψ y) volume :=
    fun g hg => (hg.mul hψ).integrable_of_hasCompactSupport (hψc.mul_left)
  -- the `m`-th coefficient: `∫ y, ((-1)^(m+n) * y^(n-m) * (n.choose m)) * ψ y`
  set c : ℕ → ℝ := fun m =>
    ∫ y, ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y with hc
  refine ⟨∑ m ∈ Finset.range (n + 1), Polynomial.monomial m (c m), ?_, ?_, ?_⟩
  · -- the convolution equals `∑ m, c m * x^m`, which is the polynomial's evaluation
    funext x
    have hsum : (fun y => (x - y) ^ n * ψ y)
        = fun y => ∑ m ∈ Finset.range (n + 1),
            (x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ))) * ψ y := by
      funext y
      rw [sub_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hsum]
    rw [MeasureTheory.integral_finsetSum]
    · simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      have hre : (fun y => x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y)
          = fun y => x ^ m * (((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y) := by
        funext y; ring
      rw [hre, MeasureTheory.integral_const_mul, mul_comm (x ^ m) (c m), hc]
    · intro m _
      have : (fun y => x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y)
          = fun y => (x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ))) * ψ y := by
        funext y; ring
      rw [this]
      exact hint _ (by fun_prop)
  · -- degree bound: each monomial has degree `≤ m ≤ n`
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
    refine (Polynomial.natDegree_monomial_le _).trans ?_
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  · -- the `n`-th coefficient picks out the `m = n` term: `c n = ∫ ψ`
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, if_pos rfl, hc]
      simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      have : (-1 : ℝ) ^ (n + n) = 1 := (Even.add_self n).neg_one_pow
      rw [this]; ring
    · intro m hm hmn
      rw [Polynomial.coeff_monomial, if_neg hmn]
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn

end ConvolutionPolynomial
