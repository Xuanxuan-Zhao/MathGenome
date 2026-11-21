import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.DirectedSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C07.Orientation
import MathGenome.Internal.MultivariableAnalysis.D04.C14.GraphTransitionsAndIntrinsicBoundary
import Mathlib.Topology.Algebra.Module.LocallyConvex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Function Topology Filter
open scoped ContDiff
set_option maxHeartbeats 800000
namespace D04.DirectedSubstitution
open Darboux JordanRegions

abbrev ProperIntegrable := @Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
abbrev coefficientIntegral := @Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
abbrev pullbackWithin := @Specs.D04.C15.DirectedSubstitution.Model.pullbackWithin

lemma regionBounded_of_continuous_compact {k : ℕ} {S : Set (E k)} {f : S → ℝ}
    (hf : Continuous f) (hk : HasCompactSupport f) : RegionBounded f := by
  exact hk.exists_bound_of_continuous hf

/-- The sign is selected on the actual source; emptiness needs no base point. -/
lemma open_sign {k : ℕ} (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hc : IsPreconnected e.source) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ x ∈ e.source, Real.sign ((fderiv ℝ e x).det) = σ := by
  rcases e.source.eq_empty_or_nonempty with hs | ⟨a, ha⟩
  · exact ⟨1, Or.inl rfl, fun x hx => False.elim (by simpa [hs] using hx)⟩
  · obtain ⟨hd, hn⟩ := Orientation.determinant_regular e he hei
    have hsign := Orientation.constant_sign hc hd hn ha
    rcases hsign with hp | hm
    · exact ⟨1, Or.inl rfl, fun x hx => Real.sign_of_pos (hp x hx)⟩
    · exact ⟨-1, Or.inr rfl, fun x hx => Real.sign_of_neg (hm x hx)⟩

theorem directed_open : Specs.D04.C15.DirectedSubstitution.directed_openType := by
  intro k e he hei hc
  obtain ⟨σ, hσ, hs⟩ := open_sign e he hei hc
  refine ⟨σ, hσ, hs, ?_⟩
  intro f hf hk
  have hi := (Localization.compact_support_integrable f e.open_target hf hk).2
  have hsub := Orientation.signed_open_substitution e he hei σ hσ hs f
    (regionBounded_of_continuous_compact hf hk) hk
  exact ⟨hi, hsub.2.2.1.mp hi, hsub.2.2.2 (Or.inl hi)⟩

theorem directed_open_component :
    Specs.D04.C15.DirectedSubstitution.directed_open_componentType := by
  intro k e he hei a ha
  dsimp only
  intro f hf hk
  let C := connectedComponentIn e.source a
  let er := e.restrOpen C e.open_source.connectedComponentIn
  have hCs : C ⊆ e.source := connectedComponentIn_subset e.source a
  have hs : er.source = C := inter_eq_right.mpr hCs
  have ht : er.target = e '' C := by
    rw [← er.image_source_eq_target, hs]
    rfl
  have hi := (Localization.compact_support_integrable f
    (ht ▸ er.open_target) hf hk).2
  have hsub := Orientation.component_open_substitution e he hei a ha f
    (regionBounded_of_continuous_compact hf hk) hk
  exact ⟨hi, hsub.2.2.1.mp hi, hsub.2.2.2 (Or.inl hi)⟩

theorem directed_zero : Specs.D04.C15.DirectedSubstitution.directed_zeroType := by
  intro U V e h f he
  have hU : IsOpen U := isOpen_discrete _
  have hV : IsOpen V := isOpen_discrete _
  have hsub := RiemannSubstitution.zero_dimension e h hU hV f
  have hg : (fun x : U =>
      pullback h (fun y => zeroExtension f y • volumeForm 0) x (standardBasis 0)) =
      fun x => f (e x) * |(fderiv ℝ h x).det| := by
    funext x
    rw [Orientation.pullback_coefficient, he x, zeroExtension_apply f (e x), hsub.1 x]
    simp only [abs_one]
  let g : U → ℝ := fun x =>
    pullback h (fun y => zeroExtension f y • volumeForm 0) x (standardBasis 0)
  change (∀ x, (fderiv ℝ h x).det = 1) ∧ ProperIntegrable f ∧ ProperIntegrable g ∧
    coefficientIntegral f = zeroExtension f 0 ∧
    coefficientIntegral g = zeroExtension g 0 ∧ coefficientIntegral g = coefficientIntegral f
  rw [show g = (fun x => f (e x) * |(fderiv ℝ h x).det|) from hg]
  exact ⟨hsub.1, hsub.2.1.2, hsub.2.2.1.2,
    hsub.2.2.2.1, hsub.2.2.2.2.1, hsub.2.2.2.2.2.symm⟩

theorem empty_integral : Specs.D04.C15.DirectedSubstitution.empty_integralType := by
  intro k f
  have hz : zeroExtension f = (fun _ : E k => (0 : ℝ)) := by
    funext x
    exact zeroExtension_of_not_mem f (fun hx => hx)
  have hb : Bornology.IsBounded (support (zeroExtension f)) := by
    simpa [hz] using (Bornology.isBounded_empty : Bornology.IsBounded (∅ : Set (E k)))
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded _).mpr hb
  have hi : Integrable (zeroExtension f) Q := by
    rw [hz]
    exact integrable_const Q 0
  have hp : ProperIntegrable f := ⟨hb, Q, hQ, hi⟩
  refine ⟨hp, ?_⟩
  obtain ⟨hi', hv⟩ := open_integral_eq_on_enclosing_box f ⟨isOpen_empty, hp⟩ Q hQ
  change openIntegral f = 0
  rw [hv]
  change lowerIntegral (zeroExtension f) Q = 0
  rw [hz]
  exact (constant_integrals Q 0).1.trans (zero_mul _)

/-- Away from the flat face a relative half-space domain is an ambient
neighborhood. Compact support removes all artificial edges of that domain. -/
lemma halfspace_continuousAt_off_face {k : ℕ} {S : Set (E (k+1))}
    (hS : ∃ O : Set (E (k+1)), IsOpen O ∧ S = halfSpace (k+1) ∩ O)
    {f : S → ℝ} (hf : Continuous f) (hk : HasCompactSupport f)
    {x : E (k+1)} (hx : x (Fin.last k) ≠ 0) : ContinuousAt (zeroExtension f) x := by
  by_cases hxt : x ∈ tsupport (zeroExtension f)
  · obtain ⟨y, hy, rfl⟩ := (Localization.zeroExtension_tsupport hk).le hxt
    obtain ⟨O, hO, he⟩ := hS
    have hyS : (y : E (k+1)) ∈ halfSpace (k+1) ∩ O := he ▸ y.property
    have hpos : 0 < (y : E (k+1)) (Fin.last k) :=
      lt_of_le_of_ne hyS.1 (Ne.symm hx)
    have hhalf : halfSpace (k+1) ∈ 𝓝 (y : E (k+1)) := by
      apply Filter.mem_of_superset
        ((isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last k)).continuous).mem_nhds hpos)
      intro z hz
      exact le_of_lt (show 0 < z (Fin.last k) from hz)
    have hnb : S ∈ 𝓝 (y : E (k+1)) := by
      simpa only [← he] using (Filter.inter_mem hhalf (hO.mem_nhds hyS.2))
    exact ((region_continuity_iff f y).mpr hf.continuousAt).continuousAt hnb
  · exact RiemannSubstitution.continuousAt_off_tsupport _ hxt

/-- The potentially discontinuous part is a portion of one coordinate face,
which the upstream finite box-cover theorem proves has content zero. -/
theorem halfspace_integrable :
    Specs.D04.C15.DirectedSubstitution.halfspace_integrableType := by
  intro k S hS f hf hk
  have hb := (Localization.zeroExtension_compact hk).isCompact.isBounded.subset
    (subset_tsupport (zeroExtension f))
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded _).mpr hb
  have hbound := zeroExtension_bounded f (regionBounded_of_continuous_compact hf hk) Q
  have hdisc : DiscontinuityCriterion.discontinuitySet (zeroExtension f) Q ⊆
      NullCovers.coordinateFace Q (Fin.last k) 0 := by
    rintro x ⟨hxQ, hxdisc⟩
    refine ⟨hxQ, ?_⟩
    by_contra hx
    exact hxdisc (halfspace_continuousAt_off_face hS hf hk hx).continuousWithinAt
  have hface : NullCovers.ContentZero (NullCovers.coordinateFace Q (Fin.last k) 0) := by
    have h := NullCovers.finite_faces_contentZero Q {((Fin.last k), (0 : ℝ))}
    simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left] using h
  refine ⟨hb, Q, hQ, ?_⟩
  exact (DiscontinuityCriterion.integrable_iff_null_discontinuitySet (Nat.succ_pos k)
    _ Q hbound).mpr (NullCovers.null_mono hdisc (NullCovers.contentZero_null hface))

/-- The shared normalized top form is the basis determinant, in every dimension. -/
lemma volumeForm_eq_basis_det (k : ℕ) : volumeForm k = (standardBasis k).det := by
  apply AlternatingMap.ext
  intro v
  rw [volumeForm_apply, Module.Basis.det_apply]
  rfl

lemma topForm_eq_coefficient_smul {k : ℕ} (η : Covector (E k) k) :
    η = η (standardBasis k) • volumeForm k := by
  rw [volumeForm_eq_basis_det]
  exact η.eq_smul_basis_det (standardBasis k)

lemma pullbackWithin_coefficient {k : ℕ} (S : Set (E k)) (h : E k → E k)
    (a : E k → ℝ) (x : E k) :
    pullbackWithin S h (fun y => a y • volumeForm k) x (standardBasis k) =
      a (h x) * (fderivWithin ℝ h S x).det := by
  change (a (h x) • volumeForm k) (fun i => fderivWithin ℝ h S x (standardBasis k i)) = _
  simp only [smul_apply, smul_eq_mul, volumeForm_eq_basis_det]
  congr 1
  simpa only [Module.Basis.det_self, mul_one, Function.comp_def, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.det] using
    Module.Basis.det_comp (standardBasis k) (fderivWithin ℝ h S x).toLinearMap (standardBasis k)

lemma pullbackWithin_eq_pullback {k : ℕ} {S : Set (E k)} (hS : IsOpen S)
    (h : E k → E k) (η : FormField k k) {x : E k} (hx : x ∈ S) :
    pullbackWithin S h η x = pullback h η x := by
  change (η (h x)).compLinearMap (fderivWithin ℝ h S x).toLinearMap =
    (η (h x)).compLinearMap (fderiv ℝ h x).toLinearMap
  rw [fderivWithin_of_isOpen hS hx]

/-- The within derivative is continuous and nonsingular all the way to the face. -/
lemma chart_determinant_regular {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n) :
    ContinuousOn (fun x => (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det)
      (chartOverlap c d) ∧
    ∀ x ∈ chartOverlap c d,
      (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det ≠ 0 := by
  refine ⟨ContinuousLinearMap.continuous_det.comp_continuousOn
    ((chart_transition_regular c d hr hkn).1.continuousOn_fderivWithin
      (EmbeddedChart.overlap_uniqueDiff c d) hr.1), ?_⟩
  intro x hx
  obtain ⟨A, hA, _⟩ := chart_transition_derivatives c d hr hkn x hx
  rw [hA.fderivWithin (EmbeddedChart.overlap_uniqueDiff c d x hx)]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

lemma chart_sign {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    (hc : IsPreconnected (chartOverlap c d)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ x ∈ chartOverlap c d,
        Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det) = σ := by
  rcases (chartOverlap c d).eq_empty_or_nonempty with hs | ⟨a, ha⟩
  · exact ⟨1, Or.inl rfl, fun x hx => False.elim (by simpa [hs] using hx)⟩
  · obtain ⟨hd, hn⟩ := chart_determinant_regular c d hr hkn
    rcases Orientation.constant_sign hc hd hn ha with hp | hm
    · exact ⟨1, Or.inl rfl, fun x hx => Real.sign_of_pos (hp x hx)⟩
    · exact ⟨-1, Or.inr rfl, fun x hx => Real.sign_of_neg (hm x hx)⟩

/-- Changing only the represented domain while preserving the ambient zero
extension preserves both proper integrability and the actual integral value. -/
lemma proper_congr {k : ℕ} {S T : Set (E k)} {f : S → ℝ} {g : T → ℝ}
    (h : zeroExtension f = zeroExtension g) :
    (ProperIntegrable f ↔ ProperIntegrable g) ∧ coefficientIntegral f = coefficientIntegral g := by
  constructor
  · change (Bornology.IsBounded (support (zeroExtension f)) ∧
      ∃ Q, Encloses (support (zeroExtension f)) Q ∧ Integrable (zeroExtension f) Q) ↔
      (Bornology.IsBounded (support (zeroExtension g)) ∧
      ∃ Q, Encloses (support (zeroExtension g)) Q ∧ Integrable (zeroExtension g) Q)
    rw [h]
  · change lowerIntegral (zeroExtension f) (enclosingBox (support (zeroExtension f))) =
      lowerIntegral (zeroExtension g) (enclosingBox (support (zeroExtension g)))
    rw [h]

lemma proper_on_box {k : ℕ} {S : Set (E k)} {f : S → ℝ} (hf : ProperIntegrable f)
    (Q : Box k) (hQ : Encloses (support (zeroExtension f)) Q) :
    ∃ hi : Integrable (zeroExtension f) Q,
      coefficientIntegral f = integral (zeroExtension f) Q hi := by
  let F : ↥(univ : Set (E k)) → ℝ := fun x => zeroExtension f x
  have hF : zeroExtension F = zeroExtension f := by
    funext x
    exact zeroExtension_apply F ⟨x, mem_univ x⟩
  have hp := (proper_congr hF).1.mpr hf
  obtain ⟨hi, hv⟩ := open_integral_eq_on_enclosing_box F ⟨isOpen_univ, hp⟩ Q (hF ▸ hQ)
  refine ⟨hF ▸ hi, ?_⟩
  change coefficientIntegral f = lowerIntegral (zeroExtension f) Q
  exact (proper_congr hF).2.symm.trans (hv.trans (by change lowerIntegral (zeroExtension F) Q = lowerIntegral (zeroExtension f) Q; rw [hF]))

/-- Coefficient integrability uses the support rather than boundedness of S. -/
lemma parameter_integrable {k : ℕ} {S : Set (E k)} (half : Bool)
    (hS : ∃ O : Set (E k), IsOpen O ∧ S = parameterSpace k half ∩ O)
    {f : S → ℝ} (hf : Continuous f) (hk : HasCompactSupport f) : ProperIntegrable f := by
  cases half with
  | false =>
    obtain ⟨O, hO, hSO⟩ := hS
    have hs : S = O := by simpa [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace] using hSO
    have ho : IsOpen S := hs ▸ hO
    exact (Localization.compact_support_integrable f ho hf hk).2.2
  | true =>
    cases k with
    | zero =>
      have ho : IsOpen S := isOpen_discrete _
      exact (Localization.compact_support_integrable f ho hf hk).2.2
    | succ k => exact halfspace_integrable S (by simpa [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace] using hS) f hf hk

lemma overlap_parameter_domain {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) :
    ∃ O : Set (E k), IsOpen O ∧ chartOverlap c d = parameterSpace k c.half ∩ O := by
  obtain ⟨W, hW, he⟩ := EmbeddedChart.overlap_relatively_open c d
  obtain ⟨O, hO, hc⟩ := c.source_open
  exact ⟨O ∩ W, hO.inter hW, by rw [he, hc, inter_assoc]⟩

def overlapHomeomorph {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) : chartOverlap c d ≃ₜ chartOverlap d c where
  toFun x := ⟨chartTransition c d x, EmbeddedChart.transition_mem c d x.property⟩
  invFun y := ⟨chartTransition d c y, EmbeddedChart.transition_mem d c y.property⟩
  left_inv x := Subtype.ext (EmbeddedChart.transition_left_inv c d x.property)
  right_inv y := Subtype.ext (EmbeddedChart.transition_left_inv d c y.property)
  continuous_toFun := (EmbeddedChart.transition_continuous c d).mapsToRestrict
    (fun _ hx => EmbeddedChart.transition_mem c d hx)
  continuous_invFun := (EmbeddedChart.transition_continuous d c).mapsToRestrict
    (fun _ hx => EmbeddedChart.transition_mem d c hx)

lemma chart_pullback_continuous_compact {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    {f : chartOverlap d c → ℝ} (hf : Continuous f) (hk : HasCompactSupport f) :
    let g : chartOverlap c d → ℝ := fun x =>
      pullbackWithin (chartOverlap c d) (chartTransition c d)
        (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
    Continuous g ∧ HasCompactSupport g := by
  let e := overlapHomeomorph c d
  have hg : (fun x : chartOverlap c d =>
      pullbackWithin (chartOverlap c d) (chartTransition c d)
        (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)) =
      fun x => f (e x) * (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det := by
    funext x
    rw [pullbackWithin_coefficient]
    exact congrArg (fun t => t * (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det)
      (zeroExtension_apply f (e x))
  dsimp only
  rw [hg]
  exact ⟨(hf.comp e.continuous).mul (chart_determinant_regular c d hr hkn).1.domRestrict,
    (RiemannSubstitution.compact_pullback e hk).mul_right⟩

/-- Agreement on a relative neighborhood identifies the full boundary derivative. -/
lemma extension_derivative {k : ℕ} {S W : Set (E k)} {F h : E k → E k}
    (hS : UniqueDiffOn ℝ S) (hW : IsOpen W) (heq : EqOn F h (S ∩ W))
    {x : E k} (hxS : x ∈ S) (hxW : x ∈ W) (hd : DifferentiableAt ℝ F x) :
    fderiv ℝ F x = fderivWithin ℝ h S x := by
  have he : h =ᶠ[𝓝[S] x] F := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hxW)]
      with y hyS hyW
    exact (heq ⟨hyS, hyW⟩).symm
  exact ((hd.hasFDerivAt.hasFDerivWithinAt).congr_of_eventuallyEq he
    (heq ⟨hxS, hxW⟩).symm).fderivWithin (hS x hxS) |>.symm

/-- Each boundary transition admits an ordinary Euclidean diffeomorphism
around the point, agreeing with it on its actual relative domain. -/
lemma local_transition_diffeomorph {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    {a : E k} (ha : a ∈ chartOverlap c d) :
    ∃ e : OpenPartialHomeomorph (E k) (E k), a ∈ e.source ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      EqOn e (chartTransition c d) (chartOverlap c d ∩ e.source) ∧
      ∀ x ∈ chartOverlap c d ∩ e.source,
        fderiv ℝ e x = fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x := by
  obtain ⟨W, F, hW, haW, hF, he⟩ := EmbeddedChart.transition_extension c d hr hkn ha
  have hF1 := hF.of_le hr.1
  obtain ⟨A, hA, _⟩ := chart_transition_derivatives c d hr hkn a ha
  have hda := (hF1.contDiffAt (hW.mem_nhds haW)).differentiableAt (by norm_num)
  have hFA := extension_derivative (EmbeddedChart.overlap_uniqueDiff c d) hW he ha haW hda
  have hA' : fderiv ℝ F a = A.toContinuousLinearMap :=
    hFA.trans (hA.fderivWithin (EmbeddedChart.overlap_uniqueDiff c d a ha))
  obtain ⟨e, heF, hae, heW, he1, hei1⟩ := ContinuousSubstitution.local_chart F a hW hF1 haW A
    (hA' ▸ hda.hasFDerivAt)
  refine ⟨e, hae, he1, hei1, ?_, ?_⟩
  · intro x hx
    rw [heF]
    exact he ⟨hx.1, heW hx.2⟩
  · intro x hx
    rw [heF]
    exact extension_derivative (EmbeddedChart.overlap_uniqueDiff c d) hW he hx.1
      (heW hx.2) ((hF1.contDiffAt (hW.mem_nhds (heW hx.2))).differentiableAt (by norm_num))

/-- Finite continuous localization works on the actual relative parameter
space, so a support touching the flat boundary is retained. -/
lemma relative_decomposition {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (f : X → ℝ) (hf : Continuous f) (hk : HasCompactSupport f)
    (hcover : tsupport f ⊆ ⋃ i, U i) :
    ∃ (s : Finset ι) (F : s → X → ℝ),
      (∀ i, Continuous (F i) ∧ HasCompactSupport (F i) ∧ tsupport (F i) ⊆ U i) ∧
      f = fun x => ∑ i, F i x := by
  classical
  obtain ⟨s, hs⟩ := hk.isCompact.elim_finite_subcover U hU hcover
  have hc : tsupport f ⊆ ⋃ i : s, U i := by simpa only [iUnion_subtype] using hs
  obtain ⟨ρ, hρ, _⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hk.isCompact (fun i : s => U i) (fun i => hU i) (locallyFinite_of_finite _) hc
  refine ⟨s, fun i x => f x * ρ i x, ?_, ?_⟩
  · exact fun i => ⟨hf.mul (ρ i).continuous, hk.mul_right,
      tsupport_mul_subset_right.trans (hρ i)⟩
  · funext x
    by_cases hx : x ∈ tsupport f
    · have hsum : ∑ i : s, ρ i x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [← Finset.mul_sum, hsum, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]

lemma extension_regionBounded {k : ℕ} {S T : Set (E k)} {f : S → ℝ}
    (hb : RegionBounded f) : RegionBounded (fun x : T => zeroExtension f x) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨max M 0, fun x => ?_⟩
  change ‖zeroExtension f (x : E k)‖ ≤ max M 0
  by_cases hx : (x : E k) ∈ S
  · rw [zeroExtension_apply f ⟨x, hx⟩]
    exact le_max_of_le_left (hM _)
  · rw [zeroExtension_of_not_mem f hx, norm_zero]
    exact le_max_right _ _

/-- Localized Euclidean substitution for a coefficient on a chart overlap.
The coefficient is allowed to have a jump after zero extension through the
flat boundary; proper integrability was proved separately above. -/
lemma local_chart_integral {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (heq : EqOn e (chartTransition c d) (chartOverlap c d ∩ e.source))
    (hd : ∀ x ∈ chartOverlap c d ∩ e.source,
      fderiv ℝ e x = fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x)
    (σ : ℝ)
    (hsign : ∀ x ∈ chartOverlap c d,
      Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det) = σ)
    {f : chartOverlap d c → ℝ} (hf : Continuous f) (hk : HasCompactSupport f)
    (hs : ∀ y ∈ tsupport f, chartTransition d c y ∈ e.source) :
    let g : chartOverlap c d → ℝ := fun x =>
      pullbackWithin (chartOverlap c d) (chartTransition c d)
        (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
    coefficientIntegral g = σ * coefficientIntegral f := by
  let F : e.target → ℝ := fun y => zeroExtension f y
  have ht : tsupport (zeroExtension f) ⊆ e.target := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (Localization.zeroExtension_tsupport hk).le hy
    have hj := EmbeddedChart.transition_mem d c z.property
    have hzx := hs z hz
    have hez : e (chartTransition d c z) = z :=
      (heq ⟨hj, hzx⟩).trans (EmbeddedChart.transition_left_inv d c z.property)
    rw [← hez]
    exact e.map_source hzx
  have hF : zeroExtension F = zeroExtension f := by
    funext y
    by_cases hy : y ∈ e.target
    · exact zeroExtension_apply F ⟨y, hy⟩
    · rw [zeroExtension_of_not_mem F hy]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hy (ht h))).symm
  have hfi := parameter_integrable d.half (overlap_parameter_domain d c) hf hk
  have hFi : OpenIntegrable F := ⟨e.open_target, (proper_congr hF).1.mpr hfi⟩
  have hFk : HasCompactSupport F := RiemannSubstitution.compact_restrict
    (Localization.zeroExtension_compact hk) ht
  have hFb : RegionBounded F := extension_regionBounded (regionBounded_of_continuous_compact hf hk)
  let p : e.source → ℝ := fun x => F ⟨e x, e.map_source x.property⟩ * |(fderiv ℝ e x).det|
  have hsub := RiemannSubstitution.riemann_substitution e.toHomeomorphSourceTarget e e.symm
    e.open_source e.open_target he hei (fun _ => rfl) (fun _ => rfl) F hFb hFk
  have hpi : OpenIntegrable p := hsub.2.2.2.2.1.mp hFi
  have hpval : openIntegral F = openIntegral p := hsub.2.2.2.2.2 (Or.inl hFi)
  let g : chartOverlap c d → ℝ := fun x =>
    pullbackWithin (chartOverlap c d) (chartTransition c d)
      (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
  have hgx (x : chartOverlap c d) :
      g x = f (overlapHomeomorph c d x) *
        (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det := by
    rw [show g x = _ from pullbackWithin_coefficient _ _ _ _]
    exact congrArg (fun t => t * (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det)
      (zeroExtension_apply f (overlapHomeomorph c d x))
  have hxS {x : E k} (hx : x ∈ e.source) (hn : zeroExtension f (e x) ≠ 0) :
      x ∈ chartOverlap c d := by
    have hy : e x ∈ chartOverlap d c := by
      by_contra hy
      exact hn (zeroExtension_of_not_mem f hy)
    let y : chartOverlap d c := ⟨e x, hy⟩
    have hyn : f y ≠ 0 := by
      intro hz
      apply hn
      exact (zeroExtension_apply f y).trans hz
    have hyk : y ∈ tsupport f := subset_tsupport f hyn
    have hjx := hs y hyk
    have hjs := EmbeddedChart.transition_mem d c hy
    have hje : e (chartTransition d c y) = e x :=
      (heq ⟨hjs, hjx⟩).trans (EmbeddedChart.transition_left_inv d c hy)
    exact e.injOn hjx hx hje ▸ hjs
  have hext : zeroExtension g = zeroExtension (fun x => σ * p x) := by
    funext x
    by_cases hx : x ∈ e.source
    · rw [zeroExtension_apply _ ⟨x, hx⟩]
      by_cases hxS' : x ∈ chartOverlap c d
      · rw [zeroExtension_apply g ⟨x, hxS'⟩, hgx]
        have hex := heq ⟨hxS', hx⟩
        have hdx := hd x ⟨hxS', hx⟩
        have hdet : (fderiv ℝ e x).det = σ * |(fderiv ℝ e x).det| := by
          rw [hdx, ← hsign x hxS', Orientation.sign_mul_abs]
        change _ = σ * (zeroExtension f (e x) * |(fderiv ℝ e x).det|)
        have hfv : zeroExtension f (e x) = f (overlapHomeomorph c d ⟨x, hxS'⟩) :=
          hex ▸ zeroExtension_apply f (overlapHomeomorph c d ⟨x, hxS'⟩)
        rw [hfv]
        change f _ * (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det = _
        rw [← hdx]
        calc
          _ = f (overlapHomeomorph c d ⟨x, hxS'⟩) *
              (σ * |(fderiv ℝ e x).det|) := congrArg (fun t => f _ * t) hdet
          _ = _ := by ring
      · rw [zeroExtension_of_not_mem g hxS']
        have hz : zeroExtension f (e x) = 0 := by
          by_contra hn
          exact hxS' (hxS hx hn)
        change 0 = σ * (zeroExtension f (e x) * _)
        rw [hz, zero_mul, mul_zero]
    · rw [zeroExtension_of_not_mem _ hx]
      by_cases hxS' : x ∈ chartOverlap c d
      · rw [zeroExtension_apply g ⟨x, hxS'⟩, hgx]
        have hz : f (overlapHomeomorph c d ⟨x, hxS'⟩) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro ht'
          have h := hs _ ht'
          change chartTransition d c (chartTransition c d x) ∈ e.source at h
          exact hx ((EmbeddedChart.transition_left_inv c d hxS') ▸ h)
        rw [hz, zero_mul]
      · exact zeroExtension_of_not_mem g hxS'
  have hsmul := Orientation.openIntegral_smul σ hpi
  exact (proper_congr hext).2.trans
    (hsmul.2.trans (congrArg (fun z => σ * z)
      (hpval.symm.trans (proper_congr hF).2)))

lemma parameterSpace_closed (k : ℕ) (half : Bool) : IsClosed (parameterSpace k half) := by
  cases half with
  | false => exact isClosed_univ
  | true =>
    cases k with
    | zero => exact isClosed_univ
    | succ k => exact isClosed_le continuous_const (EuclideanSpace.proj (Fin.last k)).continuous

lemma parameter_locallyCompact {k : ℕ} {S : Set (E k)} (half : Bool)
    (hS : ∃ O : Set (E k), IsOpen O ∧ S = parameterSpace k half ∩ O) :
    LocallyCompactSpace S := by
  obtain ⟨O, hO, he⟩ := hS
  have h : IsLocallyClosed S := by
    rw [he]
    exact (parameterSpace_closed k half).isLocallyClosed.inter hO.isLocallyClosed
  exact h.locallyCompactSpace

lemma parameter_integral_sum {k : ℕ} {S : Set (E k)} (half : Bool)
    (hS : ∃ O : Set (E k), IsOpen O ∧ S = parameterSpace k half ∩ O)
    {ι : Type} [Fintype ι] (F : ι → S → ℝ)
    (hf : ∀ i, Continuous (F i)) (hk : ∀ i, HasCompactSupport (F i)) :
    coefficientIntegral (fun x => ∑ i, F i x) = ∑ i, coefficientIntegral (F i) := by
  classical
  let K : Set (E k) := ⋃ i, tsupport (zeroExtension (F i))
  have hK : IsCompact K := isCompact_iUnion fun i => (Localization.zeroExtension_compact (hk i)).isCompact
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded K).mpr hK.isBounded
  have hqi (i : ι) : Encloses (support (zeroExtension (F i))) Q :=
    (closure_mono ((subset_tsupport _).trans (subset_iUnion (fun j =>
      tsupport (zeroExtension (F j))) i))).trans hQ
  have hqsum : Encloses (support (zeroExtension (fun x => ∑ i, F i x))) Q := by
    apply (closure_mono (show support (zeroExtension (fun x => ∑ i, F i x)) ⊆ K from ?_)).trans hQ
    intro x hx
    by_contra hxK
    apply hx
    rw [Localization.zeroExtension_sum]
    exact Finset.sum_eq_zero fun i _ => image_eq_zero_of_notMem_tsupport
      (fun h => hxK (mem_iUnion.mpr ⟨i, h⟩))
  have hi i := parameter_integrable half hS (hf i) (hk i)
  have hsum := parameter_integrable half hS (continuous_finsetSum _ (fun i _ => hf i))
    (Localization.compact_support_sum F hk)
  obtain ⟨his, hvs⟩ := proper_on_box hsum Q hqsum
  have hival i := proper_on_box (hi i) Q (hqi i)
  choose hii hvi using hival
  rw [hvs]
  have h := Darboux.integral_sum Finset.univ (fun i => zeroExtension (F i))
    (fun i _ => hii i) (by simpa only [Localization.zeroExtension_sum] using his)
  simpa only [Finset.mem_univ, ↓reduceDIte, ← hvi, ← Localization.zeroExtension_sum] using h

theorem directed_chart : Specs.D04.C15.DirectedSubstitution.directed_chartType := by
  intro r k n M c d hr hkn hc
  classical
  obtain ⟨σ, hσ, hsign⟩ := chart_sign c d hr hkn hc
  refine ⟨σ, hσ, hsign, ?_⟩
  intro f hf hk
  let S := chartOverlap c d
  let T := chartOverlap d c
  let g : S → ℝ := fun x =>
    pullbackWithin S (chartTransition c d) (fun y => zeroExtension f y • volumeForm k)
      x (standardBasis k)
  change ProperIntegrable f ∧ ProperIntegrable g ∧ coefficientIntegral g = σ * coefficientIntegral f
  have hfi := parameter_integrable d.half (overlap_parameter_domain d c) hf hk
  have hgc := chart_pullback_continuous_compact c d hr hkn hf hk
  refine ⟨hfi, parameter_integrable c.half (overlap_parameter_domain c d) hgc.1 hgc.2, ?_⟩
  have hloc (y : T) := local_transition_diffeomorph c d hr hkn
    (EmbeddedChart.transition_mem d c y.property)
  choose e hae he hei heq hd using hloc
  let U : T → Set T := fun y => {z | chartTransition d c z ∈ (e y).source}
  have hU (y : T) : IsOpen (U y) :=
    (e y).open_source.preimage (EmbeddedChart.transition_continuous d c).domRestrict
  have hcover : tsupport f ⊆ ⋃ y, U y := by
    intro y _
    exact mem_iUnion.mpr ⟨y, hae y⟩
  letI : LocallyCompactSpace T := parameter_locallyCompact d.half (overlap_parameter_domain d c)
  obtain ⟨s, F, hF, hsum⟩ := relative_decomposition U hU f hf hk hcover
  let G : s → S → ℝ := fun i x =>
    pullbackWithin S (chartTransition c d) (fun y => zeroExtension (F i) y • volumeForm k)
      x (standardBasis k)
  have hGi (i : s) : Continuous (G i) ∧ HasCompactSupport (G i) :=
    chart_pullback_continuous_compact c d hr hkn (hF i).1 (hF i).2.1
  have hval (i : s) : coefficientIntegral (G i) = σ * coefficientIntegral (F i) :=
    local_chart_integral c d hr hkn (e i.val) (he i.val) (hei i.val) (heq i.val) (hd i.val)
      σ hsign (hF i).1 (hF i).2.1 (fun y hy => (hF i).2.2 hy)
  have hg : g = fun x => ∑ i, G i x := by
    funext x
    simp only [g, G, pullbackWithin_coefficient]
    have hfval := congrFun hsum (overlapHomeomorph c d x)
    have hzero : zeroExtension f (chartTransition c d x) =
        ∑ i, zeroExtension (F i) (chartTransition c d x) := by
      have hfs : f = fun y => ∑ i, F i y := hsum
      rw [hfs, Localization.zeroExtension_sum]
    rw [hzero, Finset.sum_mul]
  calc
    coefficientIntegral g = coefficientIntegral (fun x => ∑ i, G i x) := congrArg _ hg
    _ = ∑ i, coefficientIntegral (G i) := parameter_integral_sum c.half
      (overlap_parameter_domain c d) G (fun i => (hGi i).1) (fun i => (hGi i).2)
    _ = ∑ i, σ * coefficientIntegral (F i) := Finset.sum_congr rfl (fun i _ => hval i)
    _ = σ * ∑ i, coefficientIntegral (F i) := (Finset.mul_sum _ _ _).symm
    _ = σ * coefficientIntegral f := congrArg (fun z => σ * z)
      ((parameter_integral_sum d.half (overlap_parameter_domain d c) F
        (fun i => (hF i).1) (fun i => (hF i).2.1)).symm.trans (congrArg _ hsum.symm))

lemma parameterSpace_convex (k : ℕ) (half : Bool) : Convex ℝ (parameterSpace k half) := by
  cases half with
  | false => exact convex_univ
  | true =>
    cases k with
    | zero => exact convex_univ
    | succ k =>
      exact (convex_Ici (0 : ℝ)).linear_preimage
        (EuclideanSpace.proj (Fin.last k)).toLinearMap

lemma parameter_locallyConnected {k : ℕ} {S : Set (E k)} (half : Bool)
    (hS : ∃ O : Set (E k), IsOpen O ∧ S = parameterSpace k half ∩ O) :
    LocallyConnectedSpace S := by
  obtain ⟨O, hO, he⟩ := hS
  let P := parameterSpace k half
  let U : Set P := Subtype.val ⁻¹' O
  letI : LocallyPathConnectedSpace P := (parameterSpace_convex k half).locallyPathConnectedSpace
  letI : LocallyConnectedSpace U := (hO.preimage continuous_subtype_val).locallyConnectedSpace
  let e : U ≃ₜ S :=
    { toFun := fun x => ⟨x.val.val, he.symm ▸ ⟨x.val.property, x.property⟩⟩
      invFun := fun y => by
        have hy : (y : E k) ∈ P ∩ O := by simpa only [he] using y.property
        exact ⟨⟨y.val, hy.1⟩, hy.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact e.isQuotientMap.isCoinducing.locallyConnectedSpace

lemma component_relatively_open {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) {a : E k} (ha : a ∈ chartOverlap c d) :
    ∃ W : Set (E k), IsOpen W ∧
      connectedComponentIn (chartOverlap c d) a = chartOverlap c d ∩ W := by
  letI : LocallyConnectedSpace (chartOverlap c d) :=
    parameter_locallyConnected c.half (overlap_parameter_domain c d)
  have hc : IsOpen (connectedComponent (⟨a, ha⟩ : chartOverlap c d)) := isOpen_connectedComponent
  obtain ⟨W, hW, he⟩ := hc.image_val
  exact ⟨W, hW, by rw [connectedComponentIn_eq_image ha, he, inter_comm]⟩

lemma zeroExtension_domain_eq {k : ℕ} {S T : Set (E k)} (he : S = T)
    (f : S → ℝ) (g : T → ℝ)
    (hfg : ∀ x : S, f x = g ⟨x, he ▸ x.property⟩) : zeroExtension f = zeroExtension g := by
  funext x
  by_cases hx : x ∈ S
  · have hxT : x ∈ T := he ▸ hx
    exact (zeroExtension_apply f ⟨x, hx⟩).trans
      ((hfg ⟨x, hx⟩).trans (zeroExtension_apply g ⟨x, hxT⟩).symm)
  · have hxT : x ∉ T := fun h => hx (he.symm ▸ h)
    rw [zeroExtension_of_not_mem f hx, zeroExtension_of_not_mem g hxT]

theorem directed_chart_component :
    Specs.D04.C15.DirectedSubstitution.directed_chart_componentType := by
  intro r k n M c d hr hkn a ha
  dsimp only
  intro f hf hk
  classical
  let C := connectedComponentIn (chartOverlap c d) a
  obtain ⟨W, hW, hCW⟩ := component_relatively_open c d ha
  obtain ⟨c', hsource, _, hfun, hinv, _⟩ := embeddedChart_restrict_parameter c W hW
  have hS' : chartOverlap c' d = chartOverlap c d ∩ W := by
    change c'.source ∩ c'.toFun ⁻¹' d.ambient = (c.source ∩ c.toFun ⁻¹' d.ambient) ∩ W
    rw [hsource, hfun]
    ext x
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
  have hSC : chartOverlap c' d = C := hS'.trans hCW.symm
  have htrans : chartTransition c' d = chartTransition c d := by
    change d.invFun ∘ c'.toFun = d.invFun ∘ c.toFun
    rw [hfun]
  have htarget : chartOverlap d c' = chartTransition c d '' C := by
    ext y
    constructor
    · intro hy
      refine ⟨chartTransition d c' y, hSC ▸ EmbeddedChart.transition_mem d c' hy, ?_⟩
      rw [← htrans]
      exact EmbeddedChart.transition_left_inv d c' hy
    · rintro ⟨x, hx, rfl⟩
      have h := EmbeddedChart.transition_mem c' d (hSC.symm ▸ hx)
      simpa only [htrans] using h
  have hderiv (x : E k) (hx : x ∈ C) :
      fderivWithin ℝ (chartTransition c d) (chartOverlap c' d) x =
        fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x := by
    have hxW : x ∈ W := (show x ∈ chartOverlap c d ∩ W by simpa only [C, hCW] using hx).2
    rw [hS']
    exact fderivWithin_inter (hW.mem_nhds hxW)
  have hpre : IsPreconnected (chartOverlap c' d) := by
    rw [hSC]
    exact isPreconnected_connectedComponentIn
  obtain ⟨σ, hσ, hor, hsub⟩ := directed_chart c' d hr hkn hpre
  change ∀ x ∈ chartOverlap c' d,
    Real.sign ((fderivWithin ℝ (chartTransition c' d) (chartOverlap c' d) x).det) = σ at hor
  have horig (x : E k) (hx : x ∈ C) :
      Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det) = σ := by
    have h := hor x (by simpa only [hSC] using hx)
    rw [htrans, hderiv x hx] at h
    exact h
  have hσa := horig a (mem_connectedComponentIn ha)
  let castT := Homeomorph.setCongr htarget
  let f' : chartOverlap d c' → ℝ := f ∘ castT
  have hf' : Continuous f' := hf.comp castT.continuous
  have hk' : HasCompactSupport f' := RiemannSubstitution.compact_pullback castT hk
  have hzF : zeroExtension f' = zeroExtension f :=
    zeroExtension_domain_eq htarget f' f (fun _ => rfl)
  let g' : chartOverlap c' d → ℝ := fun x =>
    pullbackWithin (chartOverlap c' d) (chartTransition c' d)
      (fun y => zeroExtension f' y • volumeForm k) x (standardBasis k)
  let g : C → ℝ := fun x =>
    pullbackWithin (chartOverlap c d) (chartTransition c d)
      (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
  have hzG : zeroExtension g' = zeroExtension g := by
    apply zeroExtension_domain_eq hSC
    intro x
    change pullbackWithin _ _ _ _ _ = pullbackWithin _ _ _ _ _
    simp only [pullbackWithin_coefficient]
    rw [htrans, hzF, hderiv x (hSC ▸ x.property)]
  have hres := hsub f' hf' hk'
  change ProperIntegrable f' ∧ ProperIntegrable g' ∧ coefficientIntegral g' = σ * coefficientIntegral f' at hres
  change (_ = 1 ∨ _ = -1) ∧ (∀ x ∈ C, _ = _) ∧
    ProperIntegrable f ∧ ProperIntegrable g ∧ coefficientIntegral g = _ * coefficientIntegral f
  refine ⟨hσa.symm ▸ hσ, fun x hx => (horig x hx).trans hσa.symm,
    (proper_congr hzF).1.mp hres.1, (proper_congr hzG).1.mp hres.2.1, ?_⟩
  calc
    coefficientIntegral g = coefficientIntegral g' := (proper_congr hzG).2.symm
    _ = σ * coefficientIntegral f' := hres.2.2
    _ = σ * coefficientIntegral f := congrArg (fun z => σ * z) (proper_congr hzF).2
    _ = _ := congrArg (fun z => z * coefficientIntegral f) hσa.symm

end D04.DirectedSubstitution
