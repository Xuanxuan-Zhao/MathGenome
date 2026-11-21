import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.SingularValuePerturbation
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.SingularValueMinmax
import Mathlib.Tactic.Linarith

noncomputable section
namespace NumAnalysis206.SingularValuePerturbation
open MatrixDefinitions SingularValueMinmaxDefinitions

variable {K : Type*} [RCLike K] {m n : ℕ}

/-- A uniform comparison on unit vectors passes through the attained minimax
formula, using the minimizing subspace for A and its maximum for B. -/
theorem singularValue_le_of_unit_bound (A B : Mat K m n) (i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ n) (c : ℝ)
    (h : ∀ x : Vec K n, ‖x‖ = 1 →
      ‖B.toEuclideanLin x‖ ≤ ‖A.toEuclideanLin x‖ + c) :
    singularValue B i ≤ singularValue A i + c := by
  obtain ⟨_, hA⟩ := SingularValueMinmax.minmax A i hi hin
  obtain ⟨hmaxB, hB⟩ := SingularValueMinmax.minmax B i hi hin
  obtain ⟨S, hS, hSA⟩ := hA.1
  obtain ⟨r, hr⟩ := hmaxB S hS
  have hBr : singularValue B i ≤ r := hB.2 ⟨S, hS, hr⟩
  obtain ⟨x, hx, hxn, hBx⟩ := hr.1
  have hAx : ‖A.toEuclideanLin x‖ ≤ singularValue A i :=
    hSA.2 ⟨x, hx, hxn, rfl⟩
  have hcomp := h x hxn
  rw [hBx] at hcomp
  linarith

/-- W40 for every positive index in the domain. -/
theorem perturbation_in_domain (A E : Mat K m n) (i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    |singularValue (A + E) i - singularValue A i| ≤ operatorNorm E := by
  have hE (x : Vec K n) (hx : ‖x‖ = 1) :
      ‖E.toEuclideanLin x‖ ≤ operatorNorm E := by
    simpa only [hx, mul_one] using MatrixData.operatorNorm_apply_le E x
  have hadd (x : Vec K n) :
      (A + E).toEuclideanLin x = A.toEuclideanLin x + E.toEuclideanLin x := by
    simp only [map_add, LinearMap.add_apply]
  have hu := singularValue_le_of_unit_bound A (A + E) i hi hin (operatorNorm E)
    (fun x hx => by
      rw [hadd]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (hE x hx)))
  have hl := singularValue_le_of_unit_bound (A + E) A i hi hin (operatorNorm E)
    (fun x hx => by
      have hnorm := norm_sub_le (A.toEuclideanLin x + E.toEuclideanLin x)
        (E.toEuclideanLin x)
      rw [add_sub_cancel_right] at hnorm
      rw [hadd]
      linarith [hE x hx])
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- W40 with the complete canonical, domain-padded singular sequence. -/
theorem perturbation : Specs.NumAnalysis206.SingularValuePerturbation.perturbation := by
  intro K _ m n A E i
  have hpos (j : ℕ) (hj : 1 ≤ j) :
      |singularValue (A + E) j - singularValue A j| ≤ operatorNorm E := by
    by_cases hjn : j ≤ n
    · exact perturbation_in_domain A E j hj hjn
    · rw [MatrixData.singularValue_zero_of_domain_lt (A + E) j (by omega),
        MatrixData.singularValue_zero_of_domain_lt A j (by omega)]
      simpa only [sub_self, abs_zero, operatorNorm] using
        (norm_nonneg E.toEuclideanLin.toContinuousLinearMap)
  cases i with
  | zero => simpa only [singularValue, Nat.zero_sub, Nat.sub_self] using hpos 1 le_rfl
  | succ j => exact hpos (j + 1) (by omega)

end NumAnalysis206.SingularValuePerturbation
