import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.RegularizerPerturbation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03Neumann
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactIdeal
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

noncomputable section
namespace ExpandedFA.PartV.RegularizerPerturbation
open ExpandedFA
universe u v w

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Neumann inversion of I+T, without a nontriviality hypothesis. -/
private theorem inverse_add [CompleteSpace X] (T : X →L[𝕜] X) (h : ‖T‖ < 1) :
    ∃ U : X →L[𝕜] X,
      (ContinuousLinearMap.id 𝕜 X + T).comp U = ContinuousLinearMap.id 𝕜 X ∧
      U.comp (ContinuousLinearMap.id 𝕜 X + T) = ContinuousLinearMap.id 𝕜 X := by
  obtain ⟨U, _, _, _, h₁, h₂, _⟩ :=
    P1.C03Neumann.neumann_inversion 𝕜 X (-T) (by simpa using h)
  exact ⟨U, by simpa using h₁, by simpa using h₂⟩

/-- Corrected left-sided perturbation with the exact compact-defect formula. -/
theorem left_perturbation : Spec.LeftPerturbation := by
  intro 𝕜 X Y _ _ _ _ _ _ _ K R C h hcompact
  obtain ⟨U, h₁, h₂⟩ := inverse_add (R.comp C)
    (lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le R C) h)
  have hd : (U.comp R).comp (K + C) - ContinuousLinearMap.id 𝕜 X =
      U.comp (R.comp K - ContinuousLinearMap.id 𝕜 X) := by
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.comp_id]
    have hi := h₂
    rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id] at hi
    rw [← hi]
    abel
  have hc : Compactness.IsCompactLinearMap
      ((U.comp R).comp (K + C) - ContinuousLinearMap.id 𝕜 X).toLinearMap := by
    rw [hd]
    exact Compactness.compact_postcomp _ U hcompact
  refine ⟨U, h₁, h₂, ?_, hc, ?_⟩
  · rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    have := hd
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id] at this
    calc
      _ = (_ - ContinuousLinearMap.id 𝕜 _) + ContinuousLinearMap.id 𝕜 _ := by abel
      _ = _ := by rw [this]; abel
  · exact ⟨U.comp R, _, hc, (eq_add_of_sub_eq hd).trans (by
      rw [← hd]; abel)⟩

/-- Corrected right-sided perturbation with the exact compact-defect formula. -/
theorem right_perturbation : Spec.RightPerturbation := by
  intro 𝕜 X Y _ _ _ _ _ _ _ K R C h hcompact
  obtain ⟨V, h₁, h₂⟩ := inverse_add (C.comp R)
    (lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le C R) (by simpa [mul_comm] using h))
  have hd : (K + C).comp (R.comp V) - ContinuousLinearMap.id 𝕜 Y =
      (K.comp R - ContinuousLinearMap.id 𝕜 Y).comp V := by
    rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.id_comp]
    have hi := h₁
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.id_comp] at hi
    rw [← hi]
    abel
  have hc : Compactness.IsCompactLinearMap
      ((K + C).comp (R.comp V) - ContinuousLinearMap.id 𝕜 Y).toLinearMap := by
    rw [hd]
    exact Compactness.compact_precomp _ V hcompact
  refine ⟨V, h₁, h₂, ?_, hc, ?_⟩
  · rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
    have := hd
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp] at this
    calc
      _ = (_ - ContinuousLinearMap.id 𝕜 _) + ContinuousLinearMap.id 𝕜 _ := by abel
      _ = _ := by rw [this]; abel
  · exact ⟨R.comp V, _, hc, (eq_add_of_sub_eq hd).trans (by
      rw [← hd]; abel)⟩

/-- The printed threshold fails on every infinite-dimensional Banach space. -/
theorem printed_threshold_counterexample : Spec.PrintedThresholdCounterexample := by
  intro 𝕜 H _ _ _ _ hinfinite
  have : Nontrivial H := by
    by_contra h
    have : Subsingleton H := not_nontrivial_iff_subsingleton.mp h
    exact hinfinite inferInstance
  let I := ContinuousLinearMap.id 𝕜 H
  let K := (1 / 2 : 𝕜) • I
  let R := (2 : 𝕜) • I
  let C := -(1 / 2 : 𝕜) • I
  have hRK : R.comp K = I := by
    simp [R, K, I, smul_smul]
  have hKR : K.comp R = I := by
    simp [R, K, I, smul_smul]
  have hzero : K + C = 0 := by simp [K, C]
  have hnorm : ‖C‖ < ‖R‖ := by
    simp only [C, R, I, norm_smul, norm_neg, norm_div, norm_one,
      RCLike.norm_ofNat, ContinuousLinearMap.norm_id, mul_one]
    norm_num
  have hnot : ¬ Compactness.IsCompactLinearMap I.toLinearMap := by
    intro hc
    exact hinfinite (FiniteDimensional.of_isCompactOperator_id (𝕜 := 𝕜)
      ((Compactness.compact_iff_isCompactOperator I.toLinearMap).mp hc))
  have hneg (D : H →L[𝕜] H)
      (hD : Compactness.IsCompactLinearMap D.toLinearMap) (heq : D = -I) : False := by
    have hc := Compactness.compact_smul (-1 : 𝕜) D.toLinearMap hD
    rw [heq, ContinuousLinearMap.toLinearMap_neg, neg_one_smul, neg_neg] at hc
    exact hnot hc
  change ‖C‖ < ‖R‖ ∧ R.comp K = I ∧ K.comp R = I ∧ _
  refine ⟨hnorm, hRK, hKR, ?_, ?_, hzero, hnot, ?_, ?_⟩
  · rw [hRK, sub_self]
    exact Compactness.compact_zero
  · rw [hKR, sub_self]
    exact Compactness.compact_zero
  · rw [hzero]
    rintro ⟨S, D, hD, hSD⟩
    apply hneg D hD
    have heq : I + D = 0 := by simpa only [ContinuousLinearMap.comp_zero] using hSD.symm
    exact eq_neg_of_add_eq_zero_right heq
  · rw [hzero]
    rintro ⟨S, D, hD, hSD⟩
    apply hneg D hD
    have heq : I + D = 0 := by simpa only [ContinuousLinearMap.zero_comp] using hSD.symm
    exact eq_neg_of_add_eq_zero_right heq

end ExpandedFA.PartV.RegularizerPerturbation
