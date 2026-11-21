import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C10.PatchGeometryGram
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace D04.AreaIntegral
open JordanRegions PatchGeometryGram

abbrev imagePoint := @Specs.D04.C10.AreaIntegral.Model.imagePoint
abbrev areaIntegrand := @Specs.D04.C10.AreaIntegral.Model.areaIntegrand
abbrev AreaIntegrable := @Specs.D04.C10.AreaIntegral.Model.AreaIntegrable
abbrev areaIntegral := @Specs.D04.C10.AreaIntegral.Model.areaIntegral
abbrev parametrizedArea := @Specs.D04.C10.AreaIntegral.Model.parametrizedArea
abbrev parameterAreaIntegral := @Specs.D04.C10.AreaIntegral.Model.parameterAreaIntegral
abbrev areaVector := @Specs.D04.C10.AreaIntegral.Model.areaVector
abbrev fluxIntegrand := @Specs.D04.C10.AreaIntegral.Model.fluxIntegrand
abbrev FluxIntegrable := @Specs.D04.C10.AreaIntegral.Model.FluxIntegrable
abbrev fluxIntegral := @Specs.D04.C10.AreaIntegral.Model.fluxIntegral
abbrev normalFluxIntegral := @Specs.D04.C10.AreaIntegral.Model.normalFluxIntegral
abbrev oppositeNormal := @Specs.D04.C10.AreaIntegral.Model.oppositeNormal

variable {n : ℕ}

lemma continuous_imagePoint {D : Set (E 2)} {φ : E 2 → E n}
    (hφ : ContinuousOn φ D) : Continuous (imagePoint D φ) := by
  exact (continuousOn_iff_continuous_domRestrict.mp hφ).subtype_mk _

lemma bounded_of_continuous {S : Set (E n)} {V : Type} [NormedAddCommGroup V]
    (hS : IsCompact S) (f : S → V) (hf : Continuous f) : RegionBounded f := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
  exact ⟨M, fun x => hM _ ⟨x, rfl⟩⟩

lemma region_integrable_of_continuous {S : Set (E 2)} (hS : IsCompact S)
    (hJ : Jordan S) (g : S → ℝ) (hg : Continuous g) : RegionIntegrable g := by
  apply integrable_of_null_relative_discontinuities (by decide) hJ g
    (bounded_of_continuous hS g hg)
  apply NullCovers.null_mono (T := ∅) _ ExceptionalSets.null_empty
  rintro x ⟨hx, hh⟩
  exact hh hg.continuousAt

lemma continuousOn_columns {U : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (j : Fin 2) :
    ContinuousOn (fun x => columns (fderiv ℝ φ x).toLinearMap j) U := by
  exact (hφ.2.1.continuousOn_fderiv_of_isOpen hφ.1 le_rfl).clm_apply continuousOn_const

lemma continuousOn_patchJacobian {U : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) : ContinuousOn (patchJacobian φ) U := by
  have hc0 := continuousOn_columns hφ 0
  have hc1 := continuousOn_columns hφ 1
  have he (x : E 2) : patchJacobian φ x =
      Real.sqrt (‖columns (fderiv ℝ φ x).toLinearMap 0‖ ^ 2 *
        ‖columns (fderiv ℝ φ x).toLinearMap 1‖ ^ 2 -
        ⟪columns (fderiv ℝ φ x).toLinearMap 0,
          columns (fderiv ℝ φ x).toLinearMap 1⟫ ^ 2) :=
    gram_two (fderiv ℝ φ x).toLinearMap
  exact (((hc0.norm.pow 2).mul (hc1.norm.pow 2) |>.sub ((hc0.inner hc1).pow 2)).sqrt).congr
    (fun x _ => he x)

lemma continuous_areaIntegrand {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (f : φ '' D → ℝ)
    (hf : Continuous f) : Continuous (areaIntegrand D φ f) := by
  have hcφ := hφ.2.1.continuousOn.mono hDU
  have hcJ := (continuousOn_patchJacobian hφ).mono hDU
  exact (hf.comp (continuous_imagePoint hcφ)).mul
    (continuousOn_iff_continuous_domRestrict.mp hcJ)

lemma area_integrable {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (f : φ '' D → ℝ) (hf : Continuous f) : AreaIntegrable D φ f := by
  refine ⟨bounded_of_continuous (hD.image_of_continuousOn
    (hφ.2.1.continuousOn.mono hDU)) f hf, ?_⟩
  exact region_integrable_of_continuous hD hJ _ (continuous_areaIntegrand hφ hDU f hf)

lemma area_integral_formula (D : Set (E 2)) (φ : E 2 → E n) (f : φ '' D → ℝ) :
    areaIntegral D φ f = regionIntegral (fun x : D =>
      f (imagePoint D φ x) * patchJacobian φ x) := rfl

lemma area_admissible_iff (D : Set (E 2)) (φ : E 2 → E n) (f : φ '' D → ℝ) :
    AreaIntegrable D φ f ↔ RegionBounded f ∧
      RegionIntegrable (fun x : D => f (imagePoint D φ x) * patchJacobian φ x) := Iff.rfl

lemma parametrized_area_formula (D : Set (E 2)) (φ : E 2 → E n) :
    parametrizedArea D φ = areaIntegral D φ (fun _ => 1) ∧
    parametrizedArea D φ = regionIntegral (fun x : D => patchJacobian φ x) := by
  refine ⟨rfl, ?_⟩
  change regionIntegral (fun x : D => 1 * patchJacobian φ x) = _
  simp only [one_mul]

lemma parametrized_area_integrable {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U) :
    AreaIntegrable D φ (fun _ => 1) :=
  area_integrable hφ hD hJ hDU _ continuous_const

/-- Cross product continuity follows from its finite bilinear coordinate formula. -/
lemma continuous_cross : Continuous (fun p : E 3 × E 3 => cross p.1 p.2) := by
  change Continuous (fun p : E 3 × E 3 => WithLp.toLp 2
    (crossProduct (WithLp.ofLp p.1) (WithLp.ofLp p.2)))
  apply (PiLp.continuous_toLp 2 _).comp
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;>
    simp only [crossProduct, LinearMap.mk₂_apply] <;>
    fun_prop

lemma continuousOn_areaVector {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) : ContinuousOn (areaVector φ) U := by
  exact continuous_cross.comp_continuousOn
    ((continuousOn_columns hφ 0).prodMk (continuousOn_columns hφ 1))

lemma continuous_fluxIntegrand {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3)
    (hF : Continuous F) : Continuous (fluxIntegrand D φ F) := by
  exact (hF.comp (continuous_imagePoint (hφ.2.1.continuousOn.mono hDU))).inner
    (continuousOn_iff_continuous_domRestrict.mp ((continuousOn_areaVector hφ).mono hDU))

lemma flux_integrable {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (F : φ '' D → E 3) (hF : Continuous F) : FluxIntegrable D φ F := by
  refine ⟨bounded_of_continuous (hD.image_of_continuousOn
    (hφ.2.1.continuousOn.mono hDU)) F hF, ?_⟩
  exact region_integrable_of_continuous hD hJ _ (continuous_fluxIntegrand hφ hDU F hF)

lemma flux_integral_formula (D : Set (E 2)) (φ : E 2 → E 3) (F : φ '' D → E 3) :
    fluxIntegral D φ F = regionIntegral (fun x : D =>
      ⟪F (imagePoint D φ x), cross (columns (fderiv ℝ φ x).toLinearMap 0)
        (columns (fderiv ℝ φ x).toLinearMap 1)⟫) := rfl

lemma flux_admissible_iff (D : Set (E 2)) (φ : E 2 → E 3) (F : φ '' D → E 3) :
    FluxIntegrable D φ F ↔ RegionBounded F ∧
      RegionIntegrable (fluxIntegrand D φ F) := Iff.rfl

lemma areaVector_nonzero {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) {x : E 2} (hx : x ∈ U) : areaVector φ x ≠ 0 :=
  (cross_rank (fderiv ℝ φ x).toLinearMap).mpr (hφ.2.2 x hx)

lemma unitNormal_mul_jacobian {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) {x : E 2} (hx : x ∈ U) (v : E 3) :
    ⟪v, unitNormal φ x⟫ * patchJacobian φ x = ⟪v, areaVector φ x⟫ := by
  have hn : ‖areaVector φ x‖ ≠ 0 := norm_ne_zero_iff.mpr (areaVector_nonzero hφ hx)
  have hJ : patchJacobian φ x = ‖areaVector φ x‖ :=
    gram_cross (fderiv ℝ φ x).toLinearMap
  change ⟪v, ‖areaVector φ x‖⁻¹ • areaVector φ x⟫ * _ = _
  rw [hJ, inner_smul_right]
  rw [mul_comm (‖areaVector φ x‖⁻¹), mul_assoc, inv_mul_cancel₀ hn, mul_one]

lemma flux_normal_integrand {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3) :
    (fun x : D => ⟪F (imagePoint D φ x), unitNormal φ x⟫ * patchJacobian φ x) =
      fluxIntegrand D φ F := by
  funext x
  exact unitNormal_mul_jacobian hφ (hDU x.property) _

lemma flux_eq_normal_integral {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3) :
    fluxIntegral D φ F = normalFluxIntegral D φ F (unitNormal φ) := by
  change regionIntegral _ = regionIntegral _
  exact congrArg regionIntegral (flux_normal_integrand hφ hDU F).symm

lemma normal_flux_integrable {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3)
    (hF : FluxIntegrable D φ F) :
    RegionIntegrable (fun x : D =>
      ⟪F (imagePoint D φ x), unitNormal φ x⟫ * patchJacobian φ x) := by
  rw [flux_normal_integrand hφ hDU F]
  exact hF.2

lemma region_integral_neg {S : Set (E n)} (g : S → ℝ) (hg : RegionIntegrable g) :
    RegionIntegrable (fun x => -g x) ∧
      regionIntegral (fun x => -g x) = -regionIntegral g := by
  classical
  obtain ⟨M, hM⟩ := hg.1
  obtain ⟨Q, hQ, hi⟩ := hg.2
  have he : zeroExtension (fun x => -g x) = fun x => -1 * zeroExtension g x := by
    funext x
    by_cases hx : x ∈ S <;>
      simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
  have hn : Darboux.Integrable (zeroExtension (fun x => -g x)) Q := by
    rw [he]
    exact Darboux.integrable_smul (-1) hi
  have hgn : RegionIntegrable (fun x => -g x) :=
    ⟨⟨M, fun x => by simpa only [norm_neg] using hM x⟩, Q, hQ, hn⟩
  refine ⟨hgn, ?_⟩
  rw [integral_eq_on_enclosing_box _ hgn hQ hn,
    integral_eq_on_enclosing_box _ hg hQ hi]
  change Darboux.lowerIntegral _ Q = -Darboux.lowerIntegral _ Q
  rw [he]
  exact (Darboux.integral_smul (-1) hi (Darboux.integrable_smul (-1) hi)).trans
    (neg_one_mul _)

lemma opposite_normal_is_unit {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) {x : E 2} (hx : x ∈ U) :
    IsUnitNormal (tangentPlane φ x) (oppositeNormal φ x) :=
  (normal_choices hφ x hx _).mpr (Or.inr rfl)

lemma opposite_flux {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3)
    (hF : FluxIntegrable D φ F) :
    RegionIntegrable (fun x : D =>
      ⟪F (imagePoint D φ x), oppositeNormal φ x⟫ * patchJacobian φ x) ∧
    normalFluxIntegral D φ F (oppositeNormal φ) = -fluxIntegral D φ F := by
  have he : (fun x : D =>
      ⟪F (imagePoint D φ x), oppositeNormal φ x⟫ * patchJacobian φ x) =
      (fun x => -fluxIntegrand D φ F x) := by
    funext x
    change ⟪F (imagePoint D φ x), -unitNormal φ x⟫ * patchJacobian φ x = _
    rw [inner_neg_right, neg_mul, unitNormal_mul_jacobian hφ (hDU x.property)]
    rfl
  have hn := region_integral_neg (fluxIntegrand D φ F) hF.2
  constructor
  · rw [he]
    exact hn.1
  · change regionIntegral _ = -regionIntegral _
    exact (congrArg regionIntegral he).trans hn.2

lemma area_empty (φ : E 2 → E n) (f : φ '' (∅ : Set (E 2)) → ℝ) :
    AreaIntegrable ∅ φ f ∧ areaIntegral ∅ φ f = 0 := by
  have hb : RegionBounded f := by
    refine ⟨0, ?_⟩
    intro y
    obtain ⟨x, hx, _⟩ := y.property
    exact False.elim hx
  exact ⟨⟨hb, (empty_region (areaIntegrand ∅ φ f)).1⟩,
    (empty_region (areaIntegrand ∅ φ f)).2⟩

lemma parametrized_area_empty (φ : E 2 → E n) : parametrizedArea ∅ φ = 0 :=
  (area_empty φ (fun _ => 1)).2

lemma flux_empty (φ : E 2 → E 3) (F : φ '' (∅ : Set (E 2)) → E 3) :
    FluxIntegrable ∅ φ F ∧ fluxIntegral ∅ φ F = 0 := by
  have hb : RegionBounded F := by
    refine ⟨0, ?_⟩
    intro y
    obtain ⟨x, hx, _⟩ := y.property
    exact False.elim hx
  exact ⟨⟨hb, (empty_region (fluxIntegrand ∅ φ F)).1⟩,
    (empty_region (fluxIntegrand ∅ φ F)).2⟩

lemma normal_flux_empty (φ : E 2 → E 3) (F : φ '' (∅ : Set (E 2)) → E 3)
    (N : E 2 → E 3) : normalFluxIntegral ∅ φ F N = 0 :=
  (empty_region _).2

lemma bounded_areaIntegrand {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hDU : D ⊆ U)
    (f : φ '' D → ℝ) (hf : RegionBounded f) : RegionBounded (areaIntegrand D φ f) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨K, hK⟩ := bounded_of_continuous hD (fun x : D => patchJacobian φ x)
    (continuousOn_iff_continuous_domRestrict.mp ((continuousOn_patchJacobian hφ).mono hDU))
  refine ⟨max M 0 * max K 0, ?_⟩
  intro x
  change ‖f (imagePoint D φ x) * patchJacobian φ x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul ((hM _).trans (le_max_left _ _)) ((hK _).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

lemma bounded_fluxIntegrand {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hDU : D ⊆ U)
    (F : φ '' D → E 3) (hF : RegionBounded F) : RegionBounded (fluxIntegrand D φ F) := by
  obtain ⟨M, hM⟩ := hF
  obtain ⟨K, hK⟩ := bounded_of_continuous hD (fun x : D => areaVector φ x)
    (continuousOn_iff_continuous_domRestrict.mp ((continuousOn_areaVector hφ).mono hDU))
  refine ⟨max M 0 * max K 0, ?_⟩
  intro x
  change ‖⟪F (imagePoint D φ x), areaVector φ x⟫‖ ≤ _
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul ((hM _).trans (le_max_left _ _)) ((hK _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _))

lemma area_zero_volume {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hv : volume D = 0) (f : φ '' D → ℝ) (hf : RegionBounded f) :
    AreaIntegrable D φ f ∧ areaIntegral D φ f = 0 := by
  have hz := zero_volume_region hJ hv (areaIntegrand D φ f)
    (bounded_areaIntegrand hφ hD hDU f hf)
  exact ⟨⟨hf, hz.1⟩, hz.2⟩

lemma flux_zero_volume {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hv : volume D = 0) (F : φ '' D → E 3) (hF : RegionBounded F) :
    FluxIntegrable D φ F ∧ fluxIntegral D φ F = 0 := by
  have hz := zero_volume_region hJ hv (fluxIntegrand D φ F)
    (bounded_fluxIntegrand hφ hD hDU F hF)
  exact ⟨⟨hF, hz.1⟩, hz.2⟩

lemma parametrized_area_zero_volume {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hv : volume D = 0) : parametrizedArea D φ = 0 := by
  exact (area_zero_volume hφ hD hJ hDU hv (fun _ => 1)
    ⟨1, fun _ => by norm_num⟩).2

lemma volume_eq_zero_of_contentZero {D : Set (E 2)} (hJ : Jordan D)
    (hZ : NullCovers.ContentZero D) : volume D = 0 := by
  obtain ⟨Q, hQ, hi0⟩ := hJ
  have hJ : Jordan D := ⟨Q, hQ, hi0⟩
  obtain ⟨hi, hz⟩ := ExceptionalSets.zero_off_contentZero (by decide : 0 < 2)
    (indicator_bounded D Q) hZ (fun x _ hx => by
      change D.indicator (fun _ => (1 : ℝ)) x = 0
      exact Set.indicator_of_notMem hx _)
  exact (volume_eq_on_enclosing_box hJ hQ hi).trans hz

lemma area_zero_content {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hZ : NullCovers.ContentZero D) (f : φ '' D → ℝ) (hf : RegionBounded f) :
    AreaIntegrable D φ f ∧ areaIntegral D φ f = 0 :=
  area_zero_volume hφ hD hJ hDU (volume_eq_zero_of_contentZero hJ hZ) f hf

lemma flux_zero_content {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hZ : NullCovers.ContentZero D) (F : φ '' D → E 3) (hF : RegionBounded F) :
    FluxIntegrable D φ F ∧ fluxIntegral D φ F = 0 :=
  flux_zero_volume hφ hD hJ hDU (volume_eq_zero_of_contentZero hJ hZ) F hF

lemma parametrized_area_zero_content {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hZ : NullCovers.ContentZero D) : parametrizedArea D φ = 0 :=
  parametrized_area_zero_volume hφ hD hJ hDU (volume_eq_zero_of_contentZero hJ hZ)

end D04.AreaIntegral
