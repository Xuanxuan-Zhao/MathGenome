import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03Perturbation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03Neumann
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Linarith

/-!
Factor A + H = A (id + Ainv H), apply Neumann inversion on E, and
compose on the right with the supplied bounded inverse Ainv. The remainder
after the zeroth Neumann term gives the inverse-difference estimate.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C03Perturbation

theorem quantitative_perturbation :
    Spec.QuantitativePerturbation := by
  intro 𝕜 E F _ _ _ _ _ _ _ A Ainv hAAinv hAinvA H hη
  let T : E →L[𝕜] E := -Ainv.comp H
  have hT : ‖T‖ < 1 := by simpa [T] using hη
  obtain ⟨S, hsum, _, _, hleft, hright, hnorm, htail, _⟩ :=
    C03Neumann.neumann_inversion 𝕜 E T hT
  let R : F →L[𝕜] E := S.comp Ainv
  have hfactor : A + H = A.comp (ContinuousLinearMap.id 𝕜 E - T) := by
    simp only [T, sub_neg_eq_add, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_id]
    rw [← ContinuousLinearMap.comp_assoc, hAAinv, ContinuousLinearMap.id_comp]
  have hinner : Ainv.comp (A + H) = ContinuousLinearMap.id 𝕜 E - T := by
    simp [T, ContinuousLinearMap.comp_add, hAinvA]
  have hsumR : HasSum (fun n : ℕ => (T ^ n).comp Ainv) R :=
    ((ContinuousLinearMap.compL 𝕜 F E E).flip Ainv).hasSum hsum
  have hdiff : R - Ainv = (S - ContinuousLinearMap.id 𝕜 E).comp Ainv := by
    simp [R, ContinuousLinearMap.sub_comp]
  have hdiffS : ‖S - ContinuousLinearMap.id 𝕜 E‖ ≤
      ‖T‖ / (1 - ‖T‖) := by
    simpa [ContinuousLinearMap.one_def] using htail 0
  refine ⟨R, ?_, ?_, hsumR, hsumR.tsum_eq.symm, ?_, ?_, ?_⟩
  · calc
      (A + H).comp R =
          A.comp (((ContinuousLinearMap.id 𝕜 E - T).comp S).comp Ainv) := by
            rw [hfactor]
            rfl
      _ = ContinuousLinearMap.id 𝕜 F := by rw [hleft]; simpa using hAAinv
  · calc
      R.comp (A + H) = S.comp (Ainv.comp (A + H)) := rfl
      _ = ContinuousLinearMap.id 𝕜 E := by rw [hinner, hright]
  · exact hsumR.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  · calc
      ‖R‖ ≤ ‖S‖ * ‖Ainv‖ := S.opNorm_comp_le Ainv
      _ ≤ (1 / (1 - ‖T‖)) * ‖Ainv‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg Ainv)
      _ = ‖Ainv‖ / (1 - ‖Ainv.comp H‖) := by simp [T, div_eq_mul_inv, mul_comm]
  · calc
      ‖R - Ainv‖ = ‖(S - ContinuousLinearMap.id 𝕜 E).comp Ainv‖ := congrArg norm hdiff
      _ ≤ ‖S - ContinuousLinearMap.id 𝕜 E‖ * ‖Ainv‖ :=
        (S - ContinuousLinearMap.id 𝕜 E).opNorm_comp_le Ainv
      _ ≤ (‖T‖ / (1 - ‖T‖)) * ‖Ainv‖ :=
        mul_le_mul_of_nonneg_right hdiffS (norm_nonneg Ainv)
      _ = ‖Ainv.comp H‖ * ‖Ainv‖ / (1 - ‖Ainv.comp H‖) := by
        simp [T, div_eq_mul_inv, mul_right_comm]


theorem bounded_invertible_iff_two_sided :
    Spec.InvertibilityIdentification := by
  intro 𝕜 E F _ _ _ _ _ A
  exact ⟨fun h => ⟨A.inverse, h.self_comp_inverse, h.inverse_comp_self⟩,
    fun ⟨_, h₁, h₂⟩ => ContinuousLinearMap.IsInvertible.of_inverse h₁ h₂⟩

theorem inverse_perturbation : Spec.InversePerturbation := by
  intro 𝕜 E F _ _ _ _ _ _ _ A hA H hH
  obtain ⟨R, h₁, h₂, hsum, heq, hlim, hnorm, hdiff⟩ :=
    quantitative_perturbation 𝕜 E F A A.inverse hA.self_comp_inverse
      hA.inverse_comp_self H hH
  have hR : (A + H).inverse = R := ContinuousLinearMap.inverse_eq h₁ h₂
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse h₁ h₂,
    hR.symm ▸ hsum, hR.symm ▸ heq, hR.symm ▸ hlim,
    hR.symm ▸ hnorm, hR.symm ▸ hdiff⟩

section LocalEstimate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

/-- A neighborhood on which the perturbation hypothesis holds and inversion
has a uniform linear bound relative to the center. -/
theorem inverse_local_bound (A : E →L[𝕜] F) (hA : A.IsInvertible) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : E →L[𝕜] F, ‖B - A‖ < δ →
      B.IsInvertible ∧
      ‖B.inverse - A.inverse‖ ≤ (2 * ‖A.inverse‖ ^ 2) * ‖B - A‖ := by
  let a : ℝ := ‖A.inverse‖
  have ha : 0 ≤ a := norm_nonneg _
  have hpos : 0 < 2 * (a + 1) := by positivity
  refine ⟨1 / (2 * (a + 1)), by positivity, ?_⟩
  intro B hB
  have hsmall : ‖B - A‖ * (2 * (a + 1)) < 1 := (lt_div_iff₀ hpos).mp hB
  have hηle : ‖A.inverse.comp (B - A)‖ ≤ a * ‖B - A‖ :=
    A.inverse.opNorm_comp_le (B - A)
  have hη : ‖A.inverse.comp (B - A)‖ < 1 / 2 := by
    nlinarith [norm_nonneg (B - A)]
  have hadd : A + (B - A) = B := add_sub_cancel _ _
  obtain ⟨hInv, _, _, _, _, hdiff⟩ :=
    inverse_perturbation 𝕜 E F A hA (B - A) (by linarith)
  rw [hadd] at hInv hdiff
  refine ⟨hInv, hdiff.trans ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1 - ‖A.inverse.comp (B - A)‖)).2
  change ‖A.inverse.comp (B - A)‖ * a ≤
    (2 * a ^ 2 * ‖B - A‖) * (1 - ‖A.inverse.comp (B - A)‖)
  have h₁ : ‖A.inverse.comp (B - A)‖ * a ≤ a ^ 2 * ‖B - A‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hηle ha]
  have h₂ : 0 ≤ a ^ 2 * ‖B - A‖ := by positivity
  nlinarith

end LocalEstimate

theorem bounded_invertible_open : Spec.InvertibleOpen := by
  intro 𝕜 E F _ _ _ _ _ _ _
  apply Metric.isOpen_iff.2
  intro A hA
  obtain ⟨δ, hδ, hbound⟩ := inverse_local_bound A hA
  refine ⟨δ, hδ, ?_⟩
  intro B hB
  exact (hbound B (by simpa only [Metric.mem_ball, dist_eq_norm] using hB)).1

theorem inverse_continuous_on : Spec.InverseContinuous := by
  intro 𝕜 E F _ _ _ _ _ _ _ A hA
  obtain ⟨δ, hδ, hbound⟩ := inverse_local_bound A hA
  apply Metric.continuousWithinAt_iff.2
  intro ε hε
  let C : ℝ := 2 * ‖A.inverse‖ ^ 2
  have hC : 0 ≤ C := by positivity
  refine ⟨min δ (ε / (C + 1)), lt_min hδ (by positivity), ?_⟩
  intro B _ hB
  have hd : ‖B - A‖ < min δ (ε / (C + 1)) := by
    simpa only [dist_eq_norm] using hB
  have hbd := (hbound B (lt_of_lt_of_le hd (min_le_left _ _))).2
  have heps : ‖B - A‖ * (C + 1) < ε :=
    (lt_div_iff₀ (by positivity : 0 < C + 1)).mp
      (lt_of_lt_of_le hd (min_le_right _ _))
  rw [dist_eq_norm]
  change ‖B.inverse - A.inverse‖ < ε
  change ‖B.inverse - A.inverse‖ ≤ C * ‖B - A‖ at hbd
  nlinarith [norm_nonneg (B - A)]

theorem perturbation_theorem : Spec.PerturbationTheorem :=
  ⟨inverse_perturbation, bounded_invertible_open, inverse_continuous_on⟩

end ExpandedFA.P1.C03Perturbation
