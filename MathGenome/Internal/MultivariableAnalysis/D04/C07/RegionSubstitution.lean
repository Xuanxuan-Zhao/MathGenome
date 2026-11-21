import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.D04.C07.NullPreservation
import MathGenome.Internal.MultivariableAnalysis.D04.C07.RiemannSubstitution

noncomputable section
open Set Function Topology
open scoped ENNReal
namespace D04.RegionSubstitution
open Darboux JordanRegions

variable {n : ℕ} {S U : Set (E n)}

/-- Extending from a subset to an intermediate domain does not change the
ambient zero extension. -/
lemma zeroExtension_nested {V : Type} [Zero V] (hSU : S ⊆ U) (f : S → V) :
    zeroExtension (fun x : U => zeroExtension f x) = zeroExtension f := by
  funext x
  by_cases hx : x ∈ U
  · exact zeroExtension_apply _ ⟨x, hx⟩
  · rw [zeroExtension_of_not_mem _ hx,
      zeroExtension_of_not_mem f (fun hs => hx (hSU hs))]

lemma support_zeroExtension_subset {V : Type} [Zero V] (f : S → V) :
    support (zeroExtension f) ⊆ S := by
  intro x hx
  by_contra hs
  exact hx (zeroExtension_of_not_mem f hs)

lemma extended_bounded {V : Type} [NormedAddCommGroup V] (f : S → V)
    (hb : RegionBounded f) : RegionBounded (fun x : U => zeroExtension f x) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨max M 0, fun x => ?_⟩
  change ‖zeroExtension f (x : E n)‖ ≤ max M 0
  by_cases hx : (x : E n) ∈ S
  · rw [zeroExtension_apply f ⟨x, hx⟩]
    exact (hM _).trans (le_max_left _ _)
  · rw [zeroExtension_of_not_mem f hx, norm_zero]
    exact le_max_right _ _

/-- Compact closure in U, rather than mere boundedness of S, is what makes
this extension compactly supported on the open domain. -/
lemma extended_compact {V : Type} [Zero V] (f : S → V)
    (hK : IsCompact (closure S)) (hU : closure S ⊆ U) :
    HasCompactSupport (fun x : U => zeroExtension f x) := by
  apply (Localization.compact_preimage_subtype hK hU).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal
  · intro x hx
    exact subset_closure (support_zeroExtension_subset f hx)
  · exact isClosed_closure.preimage continuous_subtype_val

/-- Region integrability is equivalent to open-domain integrability of
its extension; both sides use the same ambient function. -/
lemma region_integrable_iff_open (hU : IsOpen U) (hSU : S ⊆ U)
    (hS : Bornology.IsBounded S) (f : S → ℝ) (hb : RegionBounded f) :
    RegionIntegrable f ↔ OpenIntegrable (fun x : U => zeroExtension f x) := by
  have hext := zeroExtension_nested hSU f
  have hsupp : support (zeroExtension f) ⊆ S := support_zeroExtension_subset f
  constructor
  · rintro ⟨_, Q, hQ, hi⟩
    refine ⟨hU, ?_, Q, ?_, ?_⟩
    · exact (congrArg (fun F => Bornology.IsBounded (support F)) hext).mpr
        (hS.subset hsupp)
    · exact (congrArg (fun F => Encloses (support F) Q) hext).mpr
        ((closure_mono hsupp).trans hQ)
    · exact (congrArg (fun F => Integrable F Q) hext).mpr hi
  · intro hi
    obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded S).mpr hS
    obtain ⟨hfi, _⟩ := open_integral_eq_on_enclosing_box _ hi Q (by
      rw [hext]; exact (closure_mono hsupp).trans hQ)
    exact ⟨hb, Q, hQ, (congrArg (fun F => Integrable F Q) hext).mp hfi⟩

lemma region_integral_eq_open (hSU : S ⊆ U) (f : S → ℝ) (hf : RegionIntegrable f)
    (hi : OpenIntegrable (fun x : U => zeroExtension f x)) :
    regionIntegral f = openIntegral (fun x : U => zeroExtension f x) := by
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded S).mpr (encloses_bounded hf.2.choose_spec.1)
  have hext := zeroExtension_nested hSU f
  obtain ⟨hfi, hv⟩ := open_integral_eq_on_enclosing_box _ hi Q (by
    rw [hext]; exact (closure_mono (support_zeroExtension_subset f)).trans hQ)
  have hfi' : Integrable (zeroExtension f) Q := hext ▸ hfi
  exact (integral_eq_on_enclosing_box f hf hQ hfi').trans (by simpa only [hext] using hv.symm)

/-- The image boundary and its content are handled by the upstream null
preservation theorem. Dimension zero uses Jordan evaluation directly. -/
theorem jordan_image : Specs.D04.C07.RegionSubstitution.jordan_imageType := by
  intro n e he hei S hS hK hU
  cases n with
  | zero => exact ⟨(Set.toFinite _).isCompact.isBounded, jordan_zero_dim _⟩
  | succ n =>
    have h := NullPreservation.diffeomorph_jordan (Nat.succ_pos n) e
      ((D04.crOn_iff_contDiffOn 1 e.source e e.open_source).mpr he)
      ((D04.crOn_iff_contDiffOn 1 e.target e.symm e.open_target).mpr hei) S hS hK hU
    exact ⟨h.1, h.2.1⟩

/-- Pulling back the zero extension on the target gives exactly the zero
extension of the weighted integrand on S. Injectivity is only used on
its actual source. -/
lemma weighted_extension (e : OpenPartialHomeomorph (E n) (E n))
    (hSU : S ⊆ e.source) (f : (e '' S) → ℝ) (x : e.source) :
    zeroExtension f (e x) * |(fderiv ℝ e x).det| =
      zeroExtension (fun z : S =>
        f ⟨e z, mem_image_of_mem e z.property⟩ * |(fderiv ℝ e z).det|) x := by
  by_cases hx : (x : E n) ∈ S
  · rw [zeroExtension_apply f ⟨e x, mem_image_of_mem e hx⟩]
    exact (zeroExtension_apply (fun z : S =>
      f ⟨e z, mem_image_of_mem e z.property⟩ * |(fderiv ℝ e z).det|) ⟨x, hx⟩).symm
  · have hy : e x ∉ e '' S := by
      rintro ⟨y, hy, heq⟩
      have hyx : y = x := e.injOn (hSU hy) x.property heq
      exact hx (hyx ▸ hy)
    rw [zeroExtension_of_not_mem f hy, zero_mul, zeroExtension_of_not_mem _ hx]

/-- The open-domain theorem is applied only after compact support of the
extension has been established using the image of the compact closure. -/
theorem region_substitution : Specs.D04.C07.RegionSubstitution.region_substitutionType := by
  intro n e he hei S hS hK hU f hb
  let g : S → ℝ := fun x =>
    f ⟨e x, mem_image_of_mem e x.property⟩ * |(fderiv ℝ e x).det|
  have hSU : S ⊆ e.source := subset_closure.trans hU
  have hTU : e '' S ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hSU hx)
  have hTK : IsCompact (closure (e '' S)) := by
    apply (hK.image_of_continuousOn (e.continuousOn.mono hU)).of_isClosed_subset
      isClosed_closure
    exact closure_minimal (image_mono subset_closure)
      (hK.image_of_continuousOn (e.continuousOn.mono hU)).isClosed
  have hTtarget : closure (e '' S) ⊆ e.target := by
    apply (closure_minimal (image_mono subset_closure)
      (hK.image_of_continuousOn (e.continuousOn.mono hU)).isClosed).trans
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hU hx)
  let F : e.target → ℝ := fun y => zeroExtension f y
  let G : e.source → ℝ := fun x => F (e.toHomeomorphSourceTarget x) * |(fderiv ℝ e x).det|
  have hG : G = fun x : e.source => zeroExtension g x := by
    funext x
    exact weighted_extension e hSU f x
  have hsub := RiemannSubstitution.riemann_substitution e.toHomeomorphSourceTarget e e.symm
    e.open_source e.open_target he hei (fun _ => rfl) (fun _ => rfl)
    F (extended_bounded f hb) (extended_compact f hTK hTtarget)
  have hgb : RegionBounded g := by
    obtain ⟨M, hM⟩ := hsub.1
    refine ⟨M, fun x => ?_⟩
    have h := hM ⟨x, hSU x.property⟩
    change ‖G ⟨x, hSU x.property⟩‖ ≤ M at h
    rw [hG] at h
    change ‖zeroExtension g (x : E n)‖ ≤ M at h
    simpa only [zeroExtension_apply g x] using h
  have hfi := region_integrable_iff_open e.open_target hTU (hTK.isBounded.subset subset_closure) f hb
  have hgi := region_integrable_iff_open e.open_source hSU (jordan_bounded hS) g hgb
  have hiff : RegionIntegrable f ↔ RegionIntegrable g := by
    rw [hgi, ← hG]
    exact hfi.trans hsub.2.2.2.2.1
  refine ⟨hgb, hiff, ?_⟩
  intro hi
  have hif : RegionIntegrable f := hi.elim id hiff.mpr
  have hig : RegionIntegrable g := hiff.mp hif
  have hF : OpenIntegrable F := hfi.mp hif
  have hGint : OpenIntegrable G := by rw [hG]; exact hgi.mp hig
  calc
    regionIntegral f = openIntegral F := region_integral_eq_open hTU f hif hF
    _ = openIntegral G := hsub.2.2.2.2.2 (Or.inl hF)
    _ = regionIntegral g := by
      rw [hG]
      exact (region_integral_eq_open hSU g hig (hgi.mp hig)).symm

theorem volume_substitution : Specs.D04.C07.RegionSubstitution.volume_substitutionType := by
  intro n e he hei S hS hK hU
  have hT := (jordan_image e he hei S hS hK hU).2
  let f : (e '' S) → ℝ := fun _ => 1
  have hf : RegionIntegrable f := by
    obtain ⟨Q, hQ, hi⟩ := hT
    refine ⟨⟨1, fun _ => by simp [f]⟩, Q, hQ, ?_⟩
    have hext : zeroExtension f = JordanRegions.indicator (e '' S) := by
      funext x
      by_cases hx : x ∈ e '' S
      · rw [zeroExtension_apply f ⟨x, hx⟩]
        simp only [f, JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator,
          Set.indicator_of_mem hx]
      · rw [zeroExtension_of_not_mem f hx]
        simp only [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator,
          Set.indicator_of_notMem hx]
    exact (congrArg (fun F => Integrable F Q) hext).mpr hi
  have h := region_substitution e he hei S hS hK hU f hf.1
  have hgi := h.2.1.mp hf
  have hv := h.2.2 (Or.inl hf)
  simpa only [f, one_mul, regionIntegral_one] using And.intro hgi hv

/-- The Jacobian is bounded on the compact closure; this bound is obtained
from continuity, not added as a diffeomorphism hypothesis. -/
lemma jacobian_bound (e : OpenPartialHomeomorph (E n) (E n))
    (he : ContDiffOn ℝ 1 e e.source) (hK : IsCompact (closure S))
    (hU : closure S ⊆ e.source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, |(fderiv ℝ e x).det| ≤ C := by
  have hc : ContinuousOn (fun x => |(fderiv ℝ e x).det|) (closure S) :=
    ((ContinuousLinearMap.continuous_det.comp_continuousOn
      (he.continuousOn_fderiv_of_isOpen e.open_source le_rfl)).abs).mono hU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x (subset_closure hx)
  simpa only [Real.norm_eq_abs, abs_abs] using h.trans (le_max_left C 0)

theorem vector_region_substitution :
    Specs.D04.C07.RegionSubstitution.vector_region_substitutionType := by
  intro n e he hei S hS hK hU k f hb
  let g : S → E k := fun x =>
    |(fderiv ℝ e x).det| • f ⟨e x, mem_image_of_mem e x.property⟩
  obtain ⟨M, hM⟩ := hb
  obtain ⟨C, hC, hCJ⟩ := jacobian_bound e he hK hU
  have hgb : RegionBounded g := by
    refine ⟨C * max M 0, fun x => ?_⟩
    rw [show g x = |(fderiv ℝ e x).det| • f ⟨e x, mem_image_of_mem e x.property⟩ from rfl,
      norm_smul, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul (hCJ x x.property) ((hM _).trans (le_max_left _ _))
      (norm_nonneg _) hC
  have hbcoord (i : Fin k) : RegionBounded (fun y => f y i) :=
    ⟨M, fun y => (PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (f y) i).trans (hM y)⟩
  have hcoord (i : Fin k) :
      (RegionIntegrable (fun y => f y i) ↔ RegionIntegrable (fun x => g x i)) ∧
      ((RegionIntegrable (fun y => f y i) ∨ RegionIntegrable (fun x => g x i)) →
        regionIntegral (fun y => f y i) = regionIntegral (fun x => g x i)) := by
    have h := region_substitution e he hei S hS hK hU (fun y => f y i) (hbcoord i)
    simpa only [g, PiLp.smul_apply, smul_eq_mul, mul_comm] using h.2
  have hTbounded := (jordan_image e he hei S hS hK hU).1
  have hiff : VectorRegionIntegrable f ↔ VectorRegionIntegrable g := by
    constructor
    · intro hf
      exact ⟨jordan_bounded hS, fun i => (hcoord i).1.mp (hf.2 i)⟩
    · intro hg
      exact ⟨hTbounded, fun i => (hcoord i).1.mpr (hg.2 i)⟩
  refine ⟨hgb, hiff, ?_⟩
  intro hi
  ext i
  rw [vector_coordinate, vector_coordinate]
  exact (hcoord i).2 (hi.elim (fun hf => Or.inl (hf.2 i)) (fun hg => Or.inr (hg.2 i)))

end D04.RegionSubstitution
