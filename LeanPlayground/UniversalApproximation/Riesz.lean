import Mathlib
import LeanPlayground.UniversalApproximation.Activation
import LeanPlayground.Contrib.RieszKantorovich

/-!
# Riesz representation for the Universal Approximation Theorem

This file isolates the analytic input from duality theory used by the
Universal Approximation Theorem (UAT) scaffold: every continuous linear
functional on `C(K, ℝ)` is represented by integration against a signed
(regular Borel) measure on `K`.

Mathlib provides the Riesz–Markov–Kakutani theorem for *positive* linear
functionals; the *signed* / dual-space form needed here is the substantive
gap, so `riesz_repr` is **admitted** (roadmap item 1).
-/

namespace UniversalApproximation

open MeasureTheory

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- Every continuous linear functional on `C(↥K, ℝ)` (with `↥K` compact) is order bounded:
on each order interval `[0, f]` its values are bounded above by `‖L‖ * ‖f‖`. This is the
bridge feeding `C(↥K, ℝ)` into the abstract Riesz–Kantorovich decomposition. -/
theorem continuous_isOrderBounded [CompactSpace ↥K] (L : C(↥K, ℝ) →L[ℝ] ℝ) :
    RieszKantorovich.IsOrderBounded L.toLinearMap := by
  intro f hf
  refine ⟨‖L‖ * ‖f‖, ?_⟩
  rintro y ⟨g, hg0, hgf, rfl⟩
  have hng : ‖g‖ ≤ ‖f‖ := by
    rw [ContinuousMap.norm_le _ (norm_nonneg f)]
    intro x
    have hgx0 : 0 ≤ g x := hg0 x
    have hgfx : g x ≤ f x := hgf x
    have habs : |g x| ≤ |f x| := by
      rw [abs_of_nonneg hgx0, abs_of_nonneg (le_trans hgx0 hgfx)]
      exact hgfx
    exact le_trans habs (ContinuousMap.norm_coe_le_norm f x)
  calc L.toLinearMap g = L g := rfl
    _ ≤ |L g| := le_abs_self _
    _ ≤ ‖L g‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖L‖ * ‖g‖ := L.le_opNorm g
    _ ≤ ‖L‖ * ‖f‖ := mul_le_mul_of_nonneg_left hng (norm_nonneg L)

/-- ADMITTED (roadmap item 1). Riesz representation of (C(K,ℝ))* by signed
regular Borel measures. Mathlib has Riesz–Markov–Kakutani for *positive*
functionals; the signed/dual form is the substantive gap. Cybenko 1989. -/
theorem riesz_repr (L : C(↥K, ℝ) →L[ℝ] ℝ) :
    ∃ μ : SignedMeasure ↥K,
      (∀ g : C(↥K, ℝ), L g = signedIntegral μ (⇑g)) ∧ (L = 0 ↔ μ = 0) := by
  sorry

end UniversalApproximation
