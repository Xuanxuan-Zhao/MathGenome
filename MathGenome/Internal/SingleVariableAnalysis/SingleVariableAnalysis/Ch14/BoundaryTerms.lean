import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.BoundaryTerms
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity

/-! The moving-boundary example for the proper oriented Darboux integral. -/
namespace SingleVariableAnalysis.ParameterIntegral.BoundaryTerms
open Riemann
open scoped BigOperators
namespace B
export Specs.SingleVariableAnalysis.Ch14.BoundaryTerms
  (integrand integrable integralValue integralDerivative partialDerivative leibnizContributions)
end B
namespace O
export Specs.SingleVariableAnalysis.Ch08.Oriented (realIntegrableValue realIntegralValue)
end O

/-- Every constant tagged sum is the constant times the interval length.
The all-tagged equivalence gives the actual Darboux value. -/
theorem constant_integral {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∃ h : RealIntegrable (fun _ => c) a b,
      realIntegral (fun _ => c) h = (b - a) * c := by
  apply (real_tagged_equivalence _ hab
    (boundedOnInterval_of_abs (M := |c|) (by simp)) _).mpr
  intro ε hε
  refine ⟨1, zero_lt_one, fun P ξ _ => ?_⟩
  have hs : taggedSum P ξ (fun _ => c) = (b-a) * c := by
    simp only [taggedSum, S.sumValue, smul_eq_mul, ← Finset.sum_mul, sum_cellLength]
  simpa only [show S.sumValue P ξ (fun _ => c) = (b-a) * c from hs,
    sub_self, norm_zero] using hε

/-- Sorting the endpoints retains the sign when the upper endpoint is negative. -/
theorem oriented_constant_integral (a b c : ℝ) :
    ∃ h : O.realIntegrableValue (fun _ => c) a b,
      O.realIntegralValue (fun _ => c) h = (b-a) * c := by
  obtain ⟨h, hv⟩ := constant_integral (min_le_max : min a b ≤ max a b) c
  refine ⟨h, ?_⟩
  change (if a ≤ b then realIntegral (fun _ => c) h
    else -realIntegral (fun _ => c) h) = (b-a) * c
  rw [hv]
  split_ifs with hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right (le_of_not_ge hab), max_eq_left (le_of_not_ge hab)]
    ring

theorem integrable : B.integrable := by
  intro t
  exact (oriented_constant_integral 0 t 1).choose

theorem integral_value : B.integralValue := by
  intro t h
  simpa only [B.integrand, sub_zero, mul_one] using (oriented_constant_integral 0 t 1).choose_spec

theorem integral_derivative : B.integralDerivative := by
  intro h t
  have he : (fun s => O.realIntegralValue (fun x => B.integrand x s) (h s)) =
      (fun s : ℝ => s) := funext (fun s => integral_value s (h s))
  rw [he]
  exact hasDerivAt_id t

theorem partial_derivative : B.partialDerivative := by
  intro x t
  have hd : HasDerivAt (B.integrand x) 0 t := hasDerivAt_const t 1
  exact ⟨hd, hd.deriv⟩

theorem leibniz_contributions : B.leibnizContributions := by
  intro t
  have he : (fun x => deriv (B.integrand x) t) = (fun _ : ℝ => (0 : ℝ)) :=
    funext (fun x => (partial_derivative x t).2)
  obtain ⟨hz, hv⟩ := oriented_constant_integral 0 t 0
  rw [mul_zero] at hv
  have hi : O.realIntegrableValue (fun x => deriv (B.integrand x) t) 0 t := by
    rw [he]
    exact hz
  have hiValue : O.realIntegralValue (fun x => deriv (B.integrand x) t) hi = 0 := by
    simpa only [he] using hv
  refine ⟨hi, ?_, ?_, hiValue, ?_⟩
  · simp [B.integrand]
  · simp [B.integrand]
  · intro h
    simpa [B.integrand, hiValue] using integral_derivative h t

end SingleVariableAnalysis.ParameterIntegral.BoundaryTerms
