import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableStieltjes
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathsChains
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsExistence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsAlgebra
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.VariationRules
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators ENNReal
open Set

namespace D12Complex.Stieltjes

namespace Old
export SingleVariableAnalysis.Stieltjes (continuous_bv_integral integral_unique
  interval_additivity meshLimit_of_refinementLimit integral_iff_of_le)
end Old

/-- The extended supremum has exactly the usual Mathlib BV meaning. -/
theorem totalVariation_eq_eVariationOn (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    totalVariation γ a b = eVariationOn γ (Icc a b) :=
  SingleVariableAnalysis.BV.totalVariation_eq_eVariationOn γ hab

theorem rectifiable_iff (γ : ComplexPath) :
    Rectifiable γ ↔ BoundedVariationOn γ (Icc γ.a γ.b) := by
  change totalVariation γ γ.a γ.b < ⊤ ↔ _
  rw [totalVariation_eq_eVariationOn γ γ.ordered, BoundedVariationOn, lt_top_iff_ne_top]

namespace MeshConverges

variable {a b : ℝ} {S T : (P : Partition a b) → Tags P → ℂ} {I J : ℂ}

theorem unique (hab : a ≤ b) (hI : MeshConverges S I) (hJ : MeshConverges S J) : I = J := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ₁, hd₁, h₁⟩ := hI (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hd₂, h₂⟩ := hJ (ε / 2) (half_pos hε)
  obtain ⟨P, hP⟩ := SingleVariableAnalysis.Stieltjes.exists_mesh_lt hab (lt_min hd₁ hd₂)
  obtain ⟨t⟩ := SingleVariableAnalysis.Riemann.tags_exist P
  have h₁' := h₁ P (hP.trans_le (min_le_left _ _)) t
  have h₂' := h₂ P (hP.trans_le (min_le_right _ _)) t
  have htri : ‖I - J‖ ≤ ‖S P t - I‖ + ‖S P t - J‖ := by
    simpa only [sub_add_sub_cancel, norm_sub_rev I] using
      norm_add_le (I - S P t) (S P t - J)
  linarith

theorem add (hI : MeshConverges S I) (hJ : MeshConverges T J) :
    MeshConverges (fun P t => S P t + T P t) (I + J) := by
  intro ε hε
  obtain ⟨δ₁, hd₁, h₁⟩ := hI (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hd₂, h₂⟩ := hJ (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hd₁ hd₂, fun P hP t => ?_⟩
  have h₁' := h₁ P (hP.trans_le (min_le_left _ _)) t
  have h₂' := h₂ P (hP.trans_le (min_le_right _ _)) t
  rw [add_sub_add_comm]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem const_mul (hI : MeshConverges S I) (c : ℂ) :
    MeshConverges (fun P t => c * S P t) (c * I) := by
  intro ε hε
  obtain ⟨δ, hd, hδ⟩ := hI (ε / (‖c‖ + 1)) (div_pos hε (by positivity))
  refine ⟨δ, hd, fun P hP t => ?_⟩
  rw [← mul_sub, norm_mul]
  have h := hδ P hP t
  have he := (div_mul_cancel₀ ε (show ‖c‖ + 1 ≠ 0 by positivity))
  nlinarith [norm_nonneg (S P t - I), norm_nonneg c]

end MeshConverges

/-- Sharp finite-sum estimate with complex increments. -/
theorem taggedSum_norm_le {a b : ℝ} (P : Partition a b) (t : Tags P)
    (u γ : ℝ → ℂ) (hγ : totalVariation γ a b < ⊤) {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ x ∈ Icc a b, ‖u x‖ ≤ M) :
    ‖taggedSum P t u γ‖ ≤ M * (totalVariation γ a b).toReal := by
  have hv : (∑ i : Fin P.n, ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖) ≤
      (totalVariation γ a b).toReal := by
    have h := ENNReal.toReal_mono (ne_of_lt hγ)
      (le_iSup (fun Q : Partition a b =>
        ∑ i : Fin Q.n, ENNReal.ofReal ‖γ (Q.point i.succ) - γ (Q.point i.castSucc)‖) P)
    simpa [totalVariation, ENNReal.toReal_sum, ENNReal.toReal_ofReal] using h
  calc
    ‖taggedSum P t u γ‖ ≤ ∑ i : Fin P.n,
        ‖u (t i) * (γ (P.point i.succ) - γ (P.point i.castSucc))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, M * ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hu _ (SingleVariableAnalysis.Stieltjes.tag_mem_interval P t i)) (norm_nonneg _)
    _ = M * ∑ i : Fin P.n, ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ :=
      (Finset.mul_sum ..).symm
    _ ≤ M * (totalVariation γ a b).toReal := mul_le_mul_of_nonneg_left hv hM

/-- Coordinate projections preserve finite variation with actual point values. -/
theorem coordinate_bv {a b : ℝ} (_hab : a ≤ b) (γ : ℝ → ℂ)
    (hγ : totalVariation γ a b < ⊤) (p : ℂ → ℝ)
    (hp : ∀ z : ℂ, ‖p z‖ ≤ ‖z‖) (hsub : ∀ z w, p (z - w) = p z - p w) :
    SingleVariableAnalysis.BV.HasBoundedVariation (p ∘ γ) a b := by
  apply lt_of_le_of_lt _ hγ
  apply iSup_le
  intro P
  apply le_trans _ (le_iSup (fun Q : Partition a b =>
      ∑ i : Fin Q.n, ENNReal.ofReal ‖γ (Q.point i.succ) - γ (Q.point i.castSucc)‖) P)
  apply Finset.sum_le_sum
  intro i _
  apply ENNReal.ofReal_le_ofReal
  simpa only [Function.comp_apply, ← hsub] using
    hp (γ (P.point i.succ) - γ (P.point i.castSucc))

/-- The exact coordinate decomposition, with the same partition and tags. -/
theorem taggedSum_coordinates {a b : ℝ} (P : Partition a b) (t : Tags P) (u γ : ℝ → ℂ) :
    taggedSum P t u γ =
      SingleVariableAnalysis.Stieltjes.taggedSum P t u (fun x => (γ x).re) +
        Complex.I * SingleVariableAnalysis.Stieltjes.taggedSum P t u (fun x => (γ x).im) := by
  simp only [taggedSum, SingleVariableAnalysis.Stieltjes.taggedSum,
    Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue, Complex.real_smul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := Complex.re_add_im (γ (P.point i.succ) - γ (P.point i.castSucc))
  calc
    _ = u (t i) * (((γ (P.point i.succ) - γ (P.point i.castSucc)).re : ℂ) +
      ((γ (P.point i.succ) - γ (P.point i.castSucc)).im : ℂ) * Complex.I) := by rw [h]
    _ = _ := by simp only [Complex.sub_re, Complex.sub_im]; ring

/-- Existence needs only finite variation of γ, not a derivative or even continuity. -/
theorem exists_integral {a b : ℝ} (hab : a ≤ b) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤) :
    ∃ I, HasIntegral a b u γ I := by
  have hr := coordinate_bv hab γ hγ Complex.re (fun z => by simpa using Complex.abs_re_le_norm z) Complex.sub_re
  have hi := coordinate_bv hab γ hγ Complex.im (fun z => by simpa using Complex.abs_im_le_norm z) Complex.sub_im
  obtain ⟨R, _, _, hR⟩ := Old.continuous_bv_integral hab u (fun x => (γ x).re) hu hr
  obtain ⟨J, _, _, hJ⟩ := Old.continuous_bv_integral hab u (fun x => (γ x).im) hu hi
  have h := MeshConverges.add hR (MeshConverges.const_mul hJ Complex.I)
  exact ⟨R + Complex.I * J, by simpa only [HasIntegral, taggedSum_coordinates] using h⟩

theorem hasIntegral_unique {a b : ℝ} (hab : a ≤ b) {u γ : ℝ → ℂ} {I J : ℂ}
    (hI : HasIntegral a b u γ I) (hJ : HasIntegral a b u γ J) : I = J :=
  MeshConverges.unique hab hI hJ

theorem integral_eq_of_hasIntegral {a b : ℝ} (hab : a ≤ b) {u γ : ℝ → ℂ} {I : ℂ}
    (hI : HasIntegral a b u γ I) : integral a b u γ = I := by
  unfold integral
  rw [dite_eq_left ⟨I, hI⟩]
  exact hasIntegral_unique hab (Classical.choose_spec (show ∃ J, HasIntegral a b u γ J from ⟨I,hI⟩)) hI

theorem hasIntegral_integral {a b : ℝ} (hab : a ≤ b) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤) :
    HasIntegral a b u γ (integral a b u γ) := by
  obtain ⟨I, hI⟩ := exists_integral hab u γ hu hγ
  rw [integral_eq_of_hasIntegral hab hI]
  exact hI

/-- Both arguments of the finite complex sum are complex linear. -/
theorem taggedSum_integrand_add {a b : ℝ} (P : Partition a b) (t : Tags P) (u v γ : ℝ → ℂ) :
    taggedSum P t (fun x => u x + v x) γ = taggedSum P t u γ + taggedSum P t v γ := by
  simp only [taggedSum, add_mul, Finset.sum_add_distrib]

theorem taggedSum_integrand_mul {a b : ℝ} (P : Partition a b) (t : Tags P)
    (c : ℂ) (u γ : ℝ → ℂ) :
    taggedSum P t (fun x => c * u x) γ = c * taggedSum P t u γ := by
  simp only [taggedSum, mul_assoc, Finset.mul_sum]

theorem taggedSum_integrator_add {a b : ℝ} (P : Partition a b) (t : Tags P) (u γ η : ℝ → ℂ) :
    taggedSum P t u (fun x => γ x + η x) = taggedSum P t u γ + taggedSum P t u η := by
  simp only [taggedSum, add_sub_add_comm, mul_add, Finset.sum_add_distrib]

theorem taggedSum_integrator_mul {a b : ℝ} (P : Partition a b) (t : Tags P)
    (c : ℂ) (u γ : ℝ → ℂ) :
    taggedSum P t u (fun x => c * γ x) = c * taggedSum P t u γ := by
  simp only [taggedSum, ← mul_sub, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem HasIntegral.integrand_add {a b : ℝ} {u v γ : ℝ → ℂ} {I J : ℂ}
    (hI : HasIntegral a b u γ I) (hJ : HasIntegral a b v γ J) :
    HasIntegral a b (fun x => u x + v x) γ (I + J) := by
  simpa only [HasIntegral, taggedSum_integrand_add] using MeshConverges.add hI hJ

theorem HasIntegral.integrand_mul {a b : ℝ} {u γ : ℝ → ℂ} {I : ℂ}
    (hI : HasIntegral a b u γ I) (c : ℂ) :
    HasIntegral a b (fun x => c * u x) γ (c * I) := by
  simpa only [HasIntegral, taggedSum_integrand_mul] using MeshConverges.const_mul hI c

theorem HasIntegral.integrator_add {a b : ℝ} {u γ η : ℝ → ℂ} {I J : ℂ}
    (hI : HasIntegral a b u γ I) (hJ : HasIntegral a b u η J) :
    HasIntegral a b u (fun x => γ x + η x) (I + J) := by
  simpa only [HasIntegral, taggedSum_integrator_add] using MeshConverges.add hI hJ

theorem HasIntegral.integrator_mul {a b : ℝ} {u γ : ℝ → ℂ} {I : ℂ}
    (hI : HasIntegral a b u γ I) (c : ℂ) :
    HasIntegral a b u (fun x => c * γ x) (c * I) := by
  simpa only [HasIntegral, taggedSum_integrator_mul] using MeshConverges.const_mul hI c

/-- Linearity for every pair for which the defining limits exist. -/
theorem integral_integrand_linearity {a b : ℝ} (hab : a ≤ b) (u v γ : ℝ → ℂ)
    (r s : ℂ) (hu : ∃ I, HasIntegral a b u γ I) (hv : ∃ J, HasIntegral a b v γ J) :
    integral a b (fun x => r * u x + s * v x) γ =
      r * integral a b u γ + s * integral a b v γ := by
  obtain ⟨I, hI⟩ := hu
  obtain ⟨J, hJ⟩ := hv
  rw [integral_eq_of_hasIntegral hab hI, integral_eq_of_hasIntegral hab hJ]
  exact integral_eq_of_hasIntegral hab ((hI.integrand_mul r).integrand_add (hJ.integrand_mul s))

theorem integral_integrator_linearity {a b : ℝ} (hab : a ≤ b) (u γ η : ℝ → ℂ)
    (r s : ℂ) (hγ : ∃ I, HasIntegral a b u γ I) (hη : ∃ J, HasIntegral a b u η J) :
    integral a b u (fun x => r * γ x + s * η x) =
      r * integral a b u γ + s * integral a b u η := by
  obtain ⟨I, hI⟩ := hγ
  obtain ⟨J, hJ⟩ := hη
  rw [integral_eq_of_hasIntegral hab hI, integral_eq_of_hasIntegral hab hJ]
  exact integral_eq_of_hasIntegral hab ((hI.integrator_mul r).integrator_add (hJ.integrator_mul s))

/-- Passage of the sharp complex increment bound to the mesh limit. -/
theorem HasIntegral.norm_le {a b : ℝ} (hab : a ≤ b) {u γ : ℝ → ℂ} {I : ℂ}
    (hI : HasIntegral a b u γ I) (hγ : totalVariation γ a b < ⊤)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ x ∈ Icc a b, ‖u x‖ ≤ B) :
    ‖I‖ ≤ B * (totalVariation γ a b).toReal := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hd, hδ⟩ := hI ε hε
  obtain ⟨P, hP⟩ := SingleVariableAnalysis.Stieltjes.exists_mesh_lt hab hd
  obtain ⟨t⟩ := SingleVariableAnalysis.Riemann.tags_exist P
  have hs := hδ P hP t
  have hb := taggedSum_norm_le P t u γ hγ hB hu
  have ht : ‖I‖ ≤ ‖taggedSum P t u γ - I‖ + ‖taggedSum P t u γ‖ := by
    simpa only [sub_add_cancel, norm_sub_rev I] using
      norm_add_le (I - taggedSum P t u γ) (taggedSum P t u γ)
  linarith

theorem integral_norm_le {a b : ℝ} (hab : a ≤ b) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤) :
    ‖integral a b u γ‖ ≤ (totalVariation γ a b).toReal * supNorm a b u := by
  have hb := isCompact_Icc.bddAbove_image hu.norm
  have hM : ∀ x ∈ Icc a b, ‖u x‖ ≤ supNorm a b u :=
    fun x hx => le_csSup hb (mem_image_of_mem _ hx)
  have hM0 : 0 ≤ supNorm a b u := (norm_nonneg (u a)).trans (hM a ⟨le_rfl,hab⟩)
  simpa only [mul_comm] using (hasIntegral_integral hab u γ hu hγ).norm_le hab hγ hM0 hM

/-- Auxiliary bridge to the already proved real-integrator refinement theory. -/
theorem hasIntegral_of_coordinate_integrals {a b : ℝ} (hab : a ≤ b) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc a b))
    (hr : SingleVariableAnalysis.BV.HasBoundedVariation (fun x => (γ x).re) a b)
    (hi : SingleVariableAnalysis.BV.HasBoundedVariation (fun x => (γ x).im) a b)
    {R J : ℂ}
    (hR : SingleVariableAnalysis.Stieltjes.HasIntegral a b u (fun x => (γ x).re) R)
    (hJ : SingleVariableAnalysis.Stieltjes.HasIntegral a b u (fun x => (γ x).im) J) :
    HasIntegral a b u γ (R + Complex.I * J) := by
  have hRm := Old.meshLimit_of_refinementLimit u _ hu hr
    ((Old.integral_iff_of_le a b hab u _ R).mp hR).2.2
  have hJm := Old.meshLimit_of_refinementLimit u _ hu hi
    ((Old.integral_iff_of_le a b hab u _ J).mp hJ).2.2
  simpa only [HasIntegral, taggedSum_coordinates] using
    MeshConverges.add hRm (MeshConverges.const_mul hJm Complex.I)

/-- Restriction preserves BV; this also covers singleton subintervals. -/
theorem boundedVariation_subinterval {E : Type*} [NormedAddCommGroup E]
    (F : ℝ → E) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b)
    (hF : SingleVariableAnalysis.BV.HasBoundedVariation F a b) :
    SingleVariableAnalysis.BV.HasBoundedVariation F c d := by
  apply (SingleVariableAnalysis.BV.boundedVariation_iff F hcd).mpr
  exact ((SingleVariableAnalysis.BV.boundedVariation_iff F hab).mp hF).mono
    (Icc_subset_Icc hac hdb)

theorem integral_add_subinterval {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤) :
    integral a b u γ = integral a c u γ + integral c b u γ := by
  have hab := hac.trans hcb
  have hr := coordinate_bv hab γ hγ Complex.re
    (fun z => by simpa using Complex.abs_re_le_norm z) Complex.sub_re
  have hi := coordinate_bv hab γ hγ Complex.im
    (fun z => by simpa using Complex.abs_im_le_norm z) Complex.sub_im
  obtain ⟨R, hR, _, _⟩ := Old.continuous_bv_integral hab u (fun x => (γ x).re) hu hr
  obtain ⟨J, hJ, _, _⟩ := Old.continuous_bv_integral hab u (fun x => (γ x).im) hu hi
  have hc : c ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hac,hcb⟩
  obtain ⟨R₁,R₂,hR₁,hR₂,hReq⟩ := (Old.interval_additivity a b c hc u _ R).mp hR
  obtain ⟨J₁,J₂,hJ₁,hJ₂,hJeq⟩ := (Old.interval_additivity a b c hc u _ J).mp hJ
  have hu₁ := hu.mono (Icc_subset_Icc le_rfl hcb)
  have hu₂ := hu.mono (Icc_subset_Icc hac le_rfl)
  have hr₁ := boundedVariation_subinterval _ hab hac le_rfl hcb hr
  have hr₂ := boundedVariation_subinterval _ hab hcb hac le_rfl hr
  have hi₁ := boundedVariation_subinterval _ hab hac le_rfl hcb hi
  have hi₂ := boundedVariation_subinterval _ hab hcb hac le_rfl hi
  rw [integral_eq_of_hasIntegral hab (hasIntegral_of_coordinate_integrals hab u γ hu hr hi hR hJ),
    integral_eq_of_hasIntegral hac (hasIntegral_of_coordinate_integrals hac u γ hu₁ hr₁ hi₁ hR₁ hJ₁),
    integral_eq_of_hasIntegral hcb (hasIntegral_of_coordinate_integrals hcb u γ hu₂ hr₂ hi₂ hR₂ hJ₂),
    hReq, hJeq]
  ring

theorem totalVariation_degenerate (a : ℝ) (γ : ℝ → ℂ) : totalVariation γ a a = 0 :=
  SingleVariableAnalysis.BV.totalVariation_degenerate γ a

theorem constant_of_zero_variation {a b : ℝ} (hab : a ≤ b) (γ : ℝ → ℂ)
    (hγ : totalVariation γ a b = 0) : ∀ x ∈ Icc a b, γ x = γ a := by
  intro x hx
  have hfin : SingleVariableAnalysis.BV.HasBoundedVariation γ a b := by
    change totalVariation γ a b < ⊤
    rw [hγ]; exact ENNReal.zero_lt_top
  have h := SingleVariableAnalysis.BV.norm_sub_le_totalVariation γ hab hfin hx ⟨le_rfl,hab⟩
  change ‖γ x - γ a‖ ≤ (totalVariation γ a b).toReal at h
  rw [hγ, ENNReal.toReal_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem taggedSum_of_constant {a b : ℝ} (P : Partition a b) (t : Tags P) (u γ : ℝ → ℂ)
    (z : ℂ) (hγ : ∀ x ∈ Icc a b, γ x = z) : taggedSum P t u γ = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hmem (j : Fin (P.n+1)) : P.point j ∈ Icc a b :=
    (SingleVariableAnalysis.Riemann.endpoints P).2.2 _
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  simp only [hγ _ (hmem i.succ), hγ _ (hmem i.castSucc), sub_self, mul_zero]

theorem integral_of_constant {a b : ℝ} (hab : a ≤ b) (u γ : ℝ → ℂ)
    (z : ℂ) (hγ : ∀ x ∈ Icc a b, γ x = z) : integral a b u γ = 0 := by
  apply integral_eq_of_hasIntegral hab
  intro ε hε
  refine ⟨1, zero_lt_one, fun P _ t => ?_⟩
  change ‖taggedSum P t u γ - 0‖ < ε
  rw [taggedSum_of_constant P t u γ z hγ, sub_self, norm_zero]
  exact hε

theorem integral_zero_variation {a b : ℝ} (hab : a ≤ b) (u γ : ℝ → ℂ)
    (hγ : totalVariation γ a b = 0) : integral a b u γ = 0 :=
  integral_of_constant hab u γ (γ a) (constant_of_zero_variation hab γ hγ)

theorem integral_degenerate (a : ℝ) (u γ : ℝ → ℂ) : integral a a u γ = 0 :=
  integral_zero_variation le_rfl u γ (totalVariation_degenerate a γ)

theorem exists_unique_integral (γ : ComplexPath) (hγ : Rectifiable γ) (u : ℝ → ℂ)
    (hu : ContinuousOn u (Icc γ.a γ.b)) : ∃! I, HasIntegral γ.a γ.b u γ I := by
  obtain ⟨I,hI⟩ := exists_integral γ.ordered u γ hu hγ
  exact ⟨I,hI, fun _ hJ => hasIntegral_unique γ.ordered hJ hI⟩

theorem contourIntegral_hasIntegral (γ : ComplexPath) (hγ : Rectifiable γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) :
    HasIntegral γ.a γ.b (f ∘ γ) γ (contourIntegral γ f) :=
  hasIntegral_integral γ.ordered _ _
    (hf.comp γ.continuousOn (fun x hx => ⟨x,hx,rfl⟩)) hγ

theorem contourIntegral_norm_le (γ : ComplexPath) (hγ : Rectifiable γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) :
    ‖contourIntegral γ f‖ ≤ (polygonalLength γ).toReal * sSup ((fun z => ‖f z‖) '' γ.trace) := by
  have heq : (fun x => ‖(f ∘ γ) x‖) '' Icc γ.a γ.b = (fun z => ‖f z‖) '' γ.trace := by
    rw [ComplexPath.trace, image_image]
    rfl
  simpa only [contourIntegral, polygonalLength, supNorm, heq] using
    integral_norm_le γ.ordered (f ∘ γ) γ (hf.comp γ.continuousOn (fun x hx => ⟨x,hx,rfl⟩)) hγ

theorem polygonalLength_eq_variation (γ : ComplexPath) :
    polygonalLength γ = totalVariation γ γ.a γ.b := rfl

theorem rectifiable_iff_finite_variation (γ : ComplexPath) :
    Rectifiable γ ↔ totalVariation γ γ.a γ.b < ⊤ := Iff.rfl

/-- Original continuous-integrand specialization of complex linearity. -/
theorem continuous_integrand_linearity {a b : ℝ} (hab : a ≤ b) (u v γ : ℝ → ℂ)
    (r s : ℂ) (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hγ : totalVariation γ a b < ⊤) :
    integral a b (fun x => r * u x + s * v x) γ =
      r * integral a b u γ + s * integral a b v γ :=
  integral_integrand_linearity hab u v γ r s
    (exists_integral hab u γ hu hγ) (exists_integral hab v γ hv hγ)

/-- Complex coefficients act on the actual complex integrator. -/
theorem continuous_integrator_linearity {a b : ℝ} (hab : a ≤ b) (u γ η : ℝ → ℂ)
    (r s : ℂ) (hu : ContinuousOn u (Icc a b))
    (hγ : totalVariation γ a b < ⊤) (hη : totalVariation η a b < ⊤) :
    integral a b u (fun x => r * γ x + s * η x) =
      r * integral a b u γ + s * integral a b u η :=
  integral_integrator_linearity hab u γ η r s
    (exists_integral hab u γ hu hγ) (exists_integral hab u η hu hη)

end D12Complex.Stieltjes

namespace D12Complex.RectifiableStieltjes
open Stieltjes

abbrev Partition : Specs.D12Complex.Ch03.RectifiableStieltjes.Partition_type :=
  @_root_.D12Complex.Stieltjes.Partition

abbrev Tags : Specs.D12Complex.Ch03.RectifiableStieltjes.Tags_type :=
  @_root_.D12Complex.Stieltjes.Tags

abbrev mesh : Specs.D12Complex.Ch03.RectifiableStieltjes.mesh_type :=
  @_root_.D12Complex.Stieltjes.mesh

abbrev totalVariation : Specs.D12Complex.Ch03.RectifiableStieltjes.totalVariation_type :=
  @_root_.D12Complex.Stieltjes.totalVariation

abbrev polygonalLength : Specs.D12Complex.Ch03.RectifiableStieltjes.polygonalLength_type :=
  @_root_.D12Complex.Stieltjes.polygonalLength

abbrev Rectifiable : Specs.D12Complex.Ch03.RectifiableStieltjes.Rectifiable_type :=
  @_root_.D12Complex.Stieltjes.Rectifiable

abbrev taggedSum : Specs.D12Complex.Ch03.RectifiableStieltjes.taggedSum_type :=
  @_root_.D12Complex.Stieltjes.taggedSum

abbrev MeshConverges : Specs.D12Complex.Ch03.RectifiableStieltjes.MeshConverges_type :=
  @_root_.D12Complex.Stieltjes.MeshConverges

abbrev HasIntegral : Specs.D12Complex.Ch03.RectifiableStieltjes.HasIntegral_type :=
  @_root_.D12Complex.Stieltjes.HasIntegral

abbrev integral : Specs.D12Complex.Ch03.RectifiableStieltjes.integral_type :=
  @_root_.D12Complex.Stieltjes.integral

abbrev contourIntegral : Specs.D12Complex.Ch03.RectifiableStieltjes.contourIntegral_type :=
  @_root_.D12Complex.Stieltjes.contourIntegral

abbrev supNorm : Specs.D12Complex.Ch03.RectifiableStieltjes.supNorm_type :=
  @_root_.D12Complex.Stieltjes.supNorm

end D12Complex.RectifiableStieltjes
