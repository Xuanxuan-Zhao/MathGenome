import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.Reparametrization
import MathGenome.Internal.MultivariableAnalysis.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring

noncomputable section
open Set Function Topology
open scoped RealInnerProductSpace Matrix
namespace D04.Reparametrization
open PatchGeometryGram AreaIntegral JordanRegions

variable {k n : ℕ}

lemma matrix_comp (A : E k →ₗ[ℝ] E n) (B : E k →ₗ[ℝ] E k) :
    matrixOfLinearMap (A.comp B) = matrixOfLinearMap A * matrixOfLinearMap B := by
  apply (matrixLinearEquiv n k).injective
  rw [matrix_composition, matrix_linear_roundtrip, matrix_linear_roundtrip,
    matrix_linear_roundtrip]

lemma matrix_det (B : E k →ₗ[ℝ] E k) : (matrixOfLinearMap B).det = B.det := by
  have h := LinearMap.det_toLin (standardBasis k) (matrixOfLinearMap B)
  change (matrixLinearEquiv k k (matrixOfLinearMap B)).det = _ at h
  simpa only [matrix_linear_roundtrip] using h.symm

lemma gram_comp (A : E k →ₗ[ℝ] E n) (B : E k →ₗ[ℝ] E k) :
    gramMatrix (A.comp B) = (matrixOfLinearMap B).transpose * gramMatrix A *
      matrixOfLinearMap B := by
  change (matrixOfLinearMap (A.comp B)).transpose * matrixOfLinearMap (A.comp B) = _
  rw [matrix_comp, Matrix.transpose_mul]
  change _ = (matrixOfLinearMap B).transpose *
    ((matrixOfLinearMap A).transpose * matrixOfLinearMap A) * matrixOfLinearMap B
  simp only [Matrix.mul_assoc]

lemma gramFactor_comp (A : E k →ₗ[ℝ] E n) (B : E k →ₗ[ℝ] E k) :
    gramFactor (A.comp B) = |B.det| * gramFactor A := by
  change Real.sqrt (gramMatrix (A.comp B)).det = _
  rw [gram_comp, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, matrix_det]
  rw [show B.det * (gramMatrix A).det * B.det = B.det ^ 2 * (gramMatrix A).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

lemma derivative_comp {U : Set (E k)} {φ : E k → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hU : e.target ⊆ U)
    {x : E k} (hx : x ∈ e.source) :
    fderiv ℝ (φ ∘ e) x = (fderiv ℝ φ (e x)).comp (fderiv ℝ e x) := by
  exact fderiv_comp x
    ((hφ.2.1.contDiffAt (hφ.1.mem_nhds (hU (e.map_source hx)))).differentiableAt (by norm_num))
    ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by norm_num))

lemma det_ne_zero (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {x : E k} (hx : x ∈ e.source) : (fderiv ℝ e x).det ≠ 0 :=
  RiemannSubstitution.jacobian_ne_zero e.toHomeomorphSourceTarget e e.symm
    e.open_source e.open_target he hei (fun _ => rfl) (fun _ => rfl) x hx

lemma regular_comp {U : Set (E k)} {φ : E k → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) : RegularPatch e.source (φ ∘ e) := by
  refine ⟨e.open_source, hφ.2.1.comp he (fun x hx => hU (e.map_source hx)), ?_⟩
  intro x hx
  rw [derivative_comp hφ e he hU hx]
  apply (hφ.2.2 (e x) (hU (e.map_source hx))).comp
  exact LinearMap.ker_eq_bot.mp (not_not.mp
    (LinearMap.det_eq_zero_iff_ker_ne_bot.not.mp (det_ne_zero e he hei hx)))

lemma patchGram_comp {U : Set (E k)} {φ : E k → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hU : e.target ⊆ U)
    {x : E k} (hx : x ∈ e.source) :
    patchGram (φ ∘ e) x = (matrixOfLinearMap (fderiv ℝ e x).toLinearMap).transpose *
      patchGram φ (e x) * matrixOfLinearMap (fderiv ℝ e x).toLinearMap := by
  change gramMatrix (fderiv ℝ (φ ∘ e) x).toLinearMap = _
  rw [derivative_comp hφ e he hU hx]
  exact gram_comp _ _

lemma patchJacobian_comp {U : Set (E k)} {φ : E k → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hU : e.target ⊆ U)
    {x : E k} (hx : x ∈ e.source) :
    patchJacobian (φ ∘ e) x = |(fderiv ℝ e x).det| * patchJacobian φ (e x) := by
  change gramFactor (fderiv ℝ (φ ∘ e) x).toLinearMap = _
  rw [derivative_comp hφ e he hU hx]
  exact gramFactor_comp _ _

lemma cross_comp (A : E 2 →ₗ[ℝ] E 3) (B : E 2 →ₗ[ℝ] E 2) :
    cross (columns (A.comp B) 0) (columns (A.comp B) 1) =
      B.det • cross (columns A 0) (columns A 1) := by
  have hcol (j : Fin 2) : columns (A.comp B) j =
      (matrixOfLinearMap B 0 j) • columns A 0 + (matrixOfLinearMap B 1 j) • columns A 1 := by
    change A (B (standardBasis 2 j)) = _
    rw [← (standardBasis 2).sum_repr (B (standardBasis 2 j))]
    simp only [Fin.sum_univ_two, map_add, map_smul]
    simp only [matrixOfLinearMap_apply]
    congr 1
  rw [hcol 0, hcol 1, ← matrix_det B, Matrix.det_fin_two]
  ext i
  fin_cases i <;>
    simp [cross, Specs.D04.C10.PatchGeometryGram.crossValue,
      Specs.D04.C10.PatchGeometryGram.Model.cross, crossProduct, LinearMap.mk₂_apply] <;> ring

lemma areaVector_comp {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hU : e.target ⊆ U)
    {x : E 2} (hx : x ∈ e.source) :
    areaVector (φ ∘ e) x = (fderiv ℝ e x).det • areaVector φ (e x) := by
  change cross (columns (fderiv ℝ (φ ∘ e) x).toLinearMap 0)
    (columns (fderiv ℝ (φ ∘ e) x).toLinearMap 1) = _
  rw [derivative_comp hφ e he hU hx]
  exact cross_comp _ _

lemma jordan_image (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S) (hSU : S ⊆ e.source) :
    IsCompact (e '' S) ∧ Jordan (e '' S) := by
  refine ⟨hS.image_of_continuousOn (e.continuousOn.mono hSU), ?_⟩
  exact (RegionSubstitution.jordan_image e he hei S hJ
    (by simpa only [hS.isClosed.closure_eq] using hS) (by simpa only [hS.isClosed.closure_eq] using hSU)).2

/-- The bounded-data statement uses exactly the two Riemann integrands in
the definition of area integration. The ambient f is only evaluated on the
common image and has no regularity assumption off that image. -/
theorem area_substitution_bounded {U : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (f : E n → ℝ)
    (hb : RegionBounded (fun y : φ '' (e '' S) => f y)) :
    (AreaIntegrable S (φ ∘ e) (fun y => f y) ↔
      AreaIntegrable (e '' S) φ (fun y => f y)) ∧
    ((AreaIntegrable S (φ ∘ e) (fun y => f y) ∨
      AreaIntegrable (e '' S) φ (fun y => f y)) →
      areaIntegral S (φ ∘ e) (fun y => f y) =
        areaIntegral (e '' S) φ (fun y => f y)) := by
  have hD := jordan_image e he hei hS hJ hSU
  have hDU : e '' S ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hU (e.map_source (hSU hx))
  have hb' : RegionBounded (fun y : (φ ∘ e) '' S => f y) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, fun y => ?_⟩
    apply hM ⟨y, ?_⟩
    rcases y.property with ⟨x, hx, hxy⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, hxy⟩
  have hw := RegionSubstitution.region_substitution e he hei S hJ
    (by simpa only [hS.isClosed.closure_eq] using hS) (by simpa only [hS.isClosed.closure_eq] using hSU)
    (areaIntegrand (e '' S) φ (fun y => f y))
    (bounded_areaIntegrand hφ hD.1 hDU _ hb)
  have hid : (fun x : S =>
      areaIntegrand (e '' S) φ (fun y => f y) ⟨e x, mem_image_of_mem e x.property⟩ *
        |(fderiv ℝ e x).det|) = areaIntegrand S (φ ∘ e) (fun y => f y) := by
    funext x
    change f (φ (e x)) * patchJacobian φ (e x) * |(fderiv ℝ e x).det| =
      f (φ (e x)) * patchJacobian (φ ∘ e) x
    rw [patchJacobian_comp hφ e he hU (hSU x.property)]
    ring
  dsimp only at hw
  rw [hid] at hw
  have hiff : AreaIntegrable S (φ ∘ e) (fun y => f y) ↔
      AreaIntegrable (e '' S) φ (fun y => f y) :=
    ⟨fun h => ⟨hb, hw.2.1.mpr h.2⟩, fun h => ⟨hb', hw.2.1.mp h.2⟩⟩
  refine ⟨hiff, ?_⟩
  intro hi
  exact (hw.2.2 (hi.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2))).symm

theorem area_substitution {U : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (f : E n → ℝ) (hf : ContinuousOn f (φ '' (e '' S))) :
    AreaIntegrable S (φ ∘ e) (fun y => f y) ∧
    AreaIntegrable (e '' S) φ (fun y => f y) ∧
    areaIntegral S (φ ∘ e) (fun y => f y) = areaIntegral (e '' S) φ (fun y => f y) := by
  have hD := jordan_image e he hei hS hJ hSU
  have hDU : e '' S ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hU (e.map_source (hSU hx))
  have hfi := area_integrable hφ hD.1 hD.2 hDU (fun y => f y)
    (continuousOn_iff_continuous_domRestrict.mp hf)
  have h := area_substitution_bounded hφ e he hei hU hS hJ hSU f hfi.1
  exact ⟨h.1.mpr hfi, hfi, h.2 (Or.inr hfi)⟩

lemma region_integral_smul {S : Set (E k)} (g : S → ℝ) (hg : RegionIntegrable g) (c : ℝ) :
    RegionIntegrable (fun x => c * g x) ∧
      regionIntegral (fun x => c * g x) = c * regionIntegral g := by
  classical
  obtain ⟨M, hM⟩ := hg.1
  obtain ⟨Q, hQ, hi⟩ := hg.2
  have hext : zeroExtension (fun x => c * g x) = fun x => c * zeroExtension g x := by
    funext x
    by_cases hx : x ∈ S <;>
      simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
  have hci : Darboux.Integrable (zeroExtension (fun x => c * g x)) Q := by
    rw [hext]; exact Darboux.integrable_smul c hi
  have hcg : RegionIntegrable (fun x => c * g x) :=
    ⟨⟨‖c‖ * M, fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg c)⟩,
      Q, hQ, hci⟩
  refine ⟨hcg, ?_⟩
  rw [integral_eq_on_enclosing_box _ hcg hQ hci,
    integral_eq_on_enclosing_box _ hg hQ hi]
  change Darboux.lowerIntegral _ Q = c * Darboux.lowerIntegral _ Q
  rw [hext]
  exact Darboux.integral_smul c hi (Darboux.integrable_smul c hi)

lemma determinant_sign_on_connected (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {C : Set (E k)} (hC : IsPreconnected C) (hCU : C ⊆ e.source) :
    (∀ x ∈ C, 0 < (fderiv ℝ e x).det) ∨ (∀ x ∈ C, (fderiv ℝ e x).det < 0) := by
  have hc : ContinuousOn (fun x => (fderiv ℝ e x).det) C :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (he.continuousOn_fderiv_of_isOpen e.open_source le_rfl)).mono hCU
  by_cases hp : ∀ x ∈ C, 0 < (fderiv ℝ e x).det
  · exact Or.inl hp
  right
  push Not at hp
  obtain ⟨a, ha, hna⟩ := hp
  have hneg : (fderiv ℝ e a).det < 0 := lt_of_le_of_ne hna (det_ne_zero e he hei (hCU ha))
  intro b hb
  by_contra hh
  have hbpos : 0 ≤ (fderiv ℝ e b).det := le_of_not_gt hh
  obtain ⟨z, hz, hzero⟩ := hC.intermediate_value ha hb hc ⟨hneg.le, hbpos⟩
  exact det_ne_zero e he hei (hCU hz) hzero

/-- This pointwise sign hypothesis can be imposed on any one component,
without requiring the full diffeomorphism domain to be connected. -/
theorem flux_substitution_bounded {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3)
    (hb : RegionBounded (fun y : φ '' (e '' S) => F y))
    (c : ℝ) (hc : c = 1 ∨ c = -1)
    (hsgn : ∀ x ∈ S, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|) :
    (FluxIntegrable S (φ ∘ e) (fun y => F y) ↔
      FluxIntegrable (e '' S) φ (fun y => F y)) ∧
    ((FluxIntegrable S (φ ∘ e) (fun y => F y) ∨
      FluxIntegrable (e '' S) φ (fun y => F y)) →
      fluxIntegral S (φ ∘ e) (fun y => F y) =
        c * fluxIntegral (e '' S) φ (fun y => F y)) := by
  have hc2 : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hD := jordan_image e he hei hS hJ hSU
  have hDU : e '' S ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hU (e.map_source (hSU hx))
  have hb' : RegionBounded (fun y : (φ ∘ e) '' S => F y) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, fun y => ?_⟩
    apply hM ⟨y, ?_⟩
    rcases y.property with ⟨x, hx, hxy⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, hxy⟩
  let w : S → ℝ := fun x =>
    fluxIntegrand (e '' S) φ (fun y => F y) ⟨e x, mem_image_of_mem e x.property⟩ *
      |(fderiv ℝ e x).det|
  let g : S → ℝ := fluxIntegrand S (φ ∘ e) (fun y => F y)
  have hw := RegionSubstitution.region_substitution e he hei S hJ
    (by simpa only [hS.isClosed.closure_eq] using hS) (by simpa only [hS.isClosed.closure_eq] using hSU)
    (fluxIntegrand (e '' S) φ (fun y => F y))
    (bounded_fluxIntegrand hφ hD.1 hDU _ hb)
  change RegionBounded w ∧ (RegionIntegrable _ ↔ RegionIntegrable w) ∧ _ at hw
  have hg : g = fun x => c * w x := by
    funext x
    change ⟪F (φ (e x)), areaVector (φ ∘ e) x⟫ = _
    rw [areaVector_comp hφ e he hU (hSU x.property), inner_smul_right, hsgn x x.property]
    change c * |(fderiv ℝ e x).det| * ⟪F (φ (e x)), areaVector φ (e x)⟫ =
      c * (⟪F (φ (e x)), areaVector φ (e x)⟫ * |(fderiv ℝ e x).det|)
    ring
  have hwg : w = fun x => c * g x := by
    rw [hg]; funext x; rw [← mul_assoc, hc2, one_mul]
  have hiff : FluxIntegrable S (φ ∘ e) (fun y => F y) ↔
      FluxIntegrable (e '' S) φ (fun y => F y) := by
    constructor
    · intro hi
      have hwi : RegionIntegrable w := by
        rw [hwg]; exact (region_integral_smul g hi.2 c).1
      exact ⟨hb, hw.2.1.mpr hwi⟩
    · intro hi
      have hgi : RegionIntegrable g := by
        rw [hg]; exact (region_integral_smul w (hw.2.1.mp hi.2) c).1
      exact ⟨hb', hgi⟩
  refine ⟨hiff, ?_⟩
  intro hi
  have hfi := hi.elim hiff.mp id
  have hwi := hw.2.1.mp hfi.2
  change regionIntegral g = c * regionIntegral _
  rw [hg, (region_integral_smul w hwi c).2]
  exact congrArg (c * ·) (hw.2.2 (Or.inl hfi.2)).symm

/-- Continuous vector fields give both integrals for either orientation. -/
theorem flux_substitution {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S)))
    (c : ℝ) (hc : c = 1 ∨ c = -1)
    (hsgn : ∀ x ∈ S, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|) :
    FluxIntegrable S (φ ∘ e) (fun y => F y) ∧
    FluxIntegrable (e '' S) φ (fun y => F y) ∧
    fluxIntegral S (φ ∘ e) (fun y => F y) =
      c * fluxIntegral (e '' S) φ (fun y => F y) := by
  have hD := jordan_image e he hei hS hJ hSU
  have hDU : e '' S ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hU (e.map_source (hSU hx))
  have hfi := flux_integrable hφ hD.1 hD.2 hDU (fun y => F y)
    (continuousOn_iff_continuous_domRestrict.mp hF)
  have h := flux_substitution_bounded hφ e he hei hU hS hJ hSU F hfi.1 c hc hsgn
  exact ⟨h.1.mpr hfi, hfi, h.2 (Or.inr hfi)⟩

/-- Choose chart signs against a prescribed geometric normal. This works
pointwise even when a patch or the integration region is disconnected. -/
theorem normal_chart_signs {U S : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hSU : S ⊆ U) (F N : E 3 → E 3)
    (hN : ∀ x ∈ S, IsUnitNormal (tangentPlane φ x) (N (φ x))) :
    ∃ σ : S → ℝ, (∀ x, σ x = 1 ∨ σ x = -1) ∧
      (∀ x : S, N (φ x) = σ x • unitNormal φ x) ∧
      normalFluxIntegral S φ (fun y => F y) (N ∘ φ) =
        regionIntegral (fun x : S => σ x * fluxIntegrand S φ (fun y => F y) x) := by
  classical
  have h (x : S) : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ N (φ x) = c • unitNormal φ x := by
    rcases (normal_choices hφ x (hSU x.property) _).mp (hN x x.property) with hn | hn
    · exact ⟨1, Or.inl rfl, by rw [one_smul]; exact hn⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul]; exact hn⟩
  choose σ hσ hn using h
  refine ⟨σ, hσ, hn, ?_⟩
  change regionIntegral _ = regionIntegral _
  congr 1
  funext x
  change ⟪F (φ x), N (φ x)⟫ * patchJacobian φ x = _
  rw [hn x, inner_smul_right, mul_assoc,
    unitNormal_mul_jacobian hφ (hSU x.property)]
  rfl

/-- With the same geometric normal the scalar density is F·N in both
charts. No orientation sign for h is required. The conclusion also applies
to any continuous N; the unit-normal condition is only its geometric use. -/
theorem fixed_normal_flux {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F N : E 3 → E 3)
    (hF : ContinuousOn F (φ '' (e '' S))) (hN : ContinuousOn N (φ '' (e '' S))) :
    RegionIntegrable (fun x : S =>
      ⟪F (φ (e x)), N (φ (e x))⟫ * patchJacobian (φ ∘ e) x) ∧
    RegionIntegrable (fun x : e '' S =>
      ⟪F (φ x), N (φ x)⟫ * patchJacobian φ x) ∧
    normalFluxIntegral S (φ ∘ e) (fun y => F y) (N ∘ (φ ∘ e)) =
      normalFluxIntegral (e '' S) φ (fun y => F y) (N ∘ φ) := by
  have h := area_substitution hφ e he hei hU hS hJ hSU
    (fun y => ⟪F y, N y⟫) (hF.inner hN)
  exact ⟨h.1.2, h.2.1.2, h.2.2⟩

lemma unitNormal_comp {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {x : E 2} (hx : x ∈ e.source)
    (c : ℝ) (hsgn : (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|) :
    unitNormal (φ ∘ e) x = c • unitNormal φ (e x) := by
  have ha : |(fderiv ℝ e x).det| ≠ 0 := abs_ne_zero.mpr (det_ne_zero e he hei hx)
  change ‖areaVector (φ ∘ e) x‖⁻¹ • areaVector (φ ∘ e) x =
    c • (‖areaVector φ (e x)‖⁻¹ • areaVector φ (e x))
  rw [areaVector_comp hφ e he hU hx, norm_smul, Real.norm_eq_abs,
    mul_inv_rev, smul_smul, smul_smul]
  congr 1
  conv_lhs => arg 2; rw [hsgn]
  calc
    _ = c * (|(fderiv ℝ e x).det|⁻¹ * |(fderiv ℝ e x).det|) *
        ‖areaVector φ (e x)‖⁻¹ := by ring
    _ = _ := by rw [inv_mul_cancel₀ ha, mul_one]

/-- If the old chart uses sign σ against a fixed normal, the new one
uses σc. This is pointwise, so mixed signs on different components pose
no restriction. -/
theorem chart_sign_comp {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {x : E 2} (hx : x ∈ e.source)
    (c σ : ℝ) (hc : c = 1 ∨ c = -1)
    (hsgn : (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|)
    (v : E 3) (hv : v = σ • unitNormal φ (e x)) :
    v = (σ * c) • unitNormal (φ ∘ e) x := by
  rw [unitNormal_comp hφ e he hei hU hx c hsgn, smul_smul]
  have hc2 : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
  rw [mul_assoc, hc2, mul_one]
  exact hv

/-- The same c can be used on each connected subset of the domain. In
particular take C to be any connected component and S compact inside it. -/
theorem component_sign (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {C : Set (E 2)} (hC : IsPreconnected C) (hCU : C ⊆ e.source) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
      ∀ x ∈ C, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det| := by
  rcases determinant_sign_on_connected e he hei hC hCU with hp | hn
  · exact ⟨1, Or.inl rfl, fun x hx => by rw [abs_of_pos (hp x hx), one_mul]⟩
  · refine ⟨-1, Or.inr rfl, fun x hx => ?_⟩
    rw [abs_of_neg (hn x hx)]; ring

/-- Data specified just on an image have an ambient extension that changes
neither their values, relative continuity nor boundedness. No ambient
continuity assumption is introduced by the ambient-field statements above. -/
lemma image_data_extension {A : Set (E n)} {V : Type} [NormedAddCommGroup V]
    (f : A → V) :
    (∀ x : A, zeroExtension f x = f x) ∧
    (Continuous f ↔ ContinuousOn (zeroExtension f) A) ∧
    (RegionBounded f ↔ RegionBounded (fun x : A => zeroExtension f x)) := by
  have h : (fun x : A => zeroExtension f x) = f := by
    funext x; exact zeroExtension_apply f x
  refine ⟨fun x => zeroExtension_apply f x, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    change Continuous f ↔ Continuous (fun x : A => zeroExtension f x)
    rw [h]
  · rw [h]

/-- Positive reparametrizations preserve the parameter-oriented flux. -/
theorem flux_preserving {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S)))
    (hpos : ∀ x ∈ S, 0 < (fderiv ℝ e x).det) :
    fluxIntegral S (φ ∘ e) (fun y => F y) = fluxIntegral (e '' S) φ (fun y => F y) := by
  have h := flux_substitution hφ e he hei hU hS hJ hSU F hF 1 (Or.inl rfl)
    (fun x hx => by rw [abs_of_pos (hpos x hx), one_mul])
  simpa only [one_mul] using h.2.2

/-- Negative reparametrizations negate the parameter-oriented flux. -/
theorem flux_reversing {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S)))
    (hneg : ∀ x ∈ S, (fderiv ℝ e x).det < 0) :
    fluxIntegral S (φ ∘ e) (fun y => F y) = -fluxIntegral (e '' S) φ (fun y => F y) := by
  have h := flux_substitution hφ e he hei hU hS hJ hSU F hF (-1) (Or.inr rfl)
    (fun x hx => by rw [abs_of_neg (hneg x hx)]; ring)
  simpa only [neg_one_mul] using h.2.2

/-- On a disconnected domain the sign is taken separately on C, which
may be any connected component. There is no common global-sign premise. -/
theorem flux_component {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {C : Set (E 2)} (hC : IsPreconnected C) (hCU : C ⊆ e.source)
    {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S) (hSC : S ⊆ C)
    (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S))) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
      (∀ x ∈ C, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|) ∧
      FluxIntegrable S (φ ∘ e) (fun y => F y) ∧
      FluxIntegrable (e '' S) φ (fun y => F y) ∧
      fluxIntegral S (φ ∘ e) (fun y => F y) =
        c * fluxIntegral (e '' S) φ (fun y => F y) := by
  obtain ⟨c, hc, hsgn⟩ := component_sign e he hei hC hCU
  exact ⟨c, hc, hsgn, flux_substitution hφ e he hei hU hS hJ (hSC.trans hCU)
    F hF c hc (fun x hx => hsgn x (hSC hx))⟩

end D04.Reparametrization
