import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteGeometricPatchIntegrals
import Mathlib.Order.Disjointed
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellsChainsAndIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C15.DirectedSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C15.LowerDimensionalImagesHaveZeroContent
import MathGenome.Internal.MultivariableAnalysis.D04.C15.OrientedManifoldAndDensityIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C14.FiniteCompactPartition

/-! Finite geometric integration on arbitrary Jordan parameter regions.

The proofs use only the shared Darboux integrals. Local diffeomorphisms are
localized by disjoint Jordan pieces; representative derivatives are compared
on the interior and the frontier is removed by zero content. The chart bridge
instead glues on a relative neighborhood, preserving the canonical chart
differential even at a genuine half-space boundary.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open Set Function Topology Filter
open scoped ContDiff BigOperators Classical
namespace D04.GeometricPatches
open Darboux JordanRegions
open Specs.D04.C15.FiniteGeometricPatchIntegrals
open Model

abbrev Patch := @Model.Patch
abbrev coefficient := @Model.coefficient
abbrev weightedCoefficient := @Model.weightedCoefficient
abbrev patchIntegral := @Model.patchIntegral

abbrev AmbientPartition := @Model.AmbientPartition
abbrev Seams := @Model.Seams
abbrev LocalReparametrization := @Model.LocalReparametrization
abbrev restrictPatch := @Model.restrictPatch
abbrev WeightedPatch := @Model.WeightedPatch
abbrev PatchChain := @Model.PatchChain
abbrev patchChainIntegral := @Model.patchChainIntegral
abbrev GeometricEquivalent := @Model.GeometricEquivalent
abbrev ambientRestriction := @Model.ambientRestriction

lemma region_compact {k n : ℕ} {O : Set (E n)} (P : Patch k O) :
    IsCompact (closure P.region) :=
  (jordan_bounded P.jordan).isCompact_closure

lemma continuous_integrable {k : ℕ} {S : Set (E k)} (hS : Jordan S)
    {f : E k → ℝ} (hf : ContinuousOn f (closure S)) :
    RegionIntegrable (fun x : S => f x) := by
  cases k with
  | zero => exact region_integrable_zero_dim _ _
  | succ k =>
    exact integrable_continuous_on_closure (Nat.succ_pos _) hS
      (fun x => f x) hf.domRestrict

theorem coefficient_continuous : coefficient_continuousType := by
  intro k n O P omega h
  have hf := P.regular.continuousOn
  have hd := P.regular.continuousOn_fderiv_of_isOpen P.open_domain le_rfl
  change ContinuousOn (fun x => omega (P.map x)
    (fun j => totalDerivative P.map x (standardBasis k j))) (closure P.region)
  simp_rw [formField_evaluation]
  apply continuousOn_finsetSum
  intro I _
  apply ContinuousOn.mul
  · exact ((h.2 I).comp hf P.mapsTo).mono P.contains
  · have hv : ∀ j : Fin k, CrOn 0 P.domain
        (fun x => totalDerivative P.map x (standardBasis k j)) :=
        fun j => hd.clm_apply continuousOn_const
    exact (crOn_multilinear 0 k (fun _ => E n) (dx (standardBasis n) I).toMultilinearMap
      P.domain _ P.open_domain hv).mono P.contains

lemma weighted_continuous {k n} {O : Set (E n)} (P : Patch k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega)
    (w : E n → ℝ) (hw : ContinuousOn w O) :
    ContinuousOn (weightedCoefficient P w omega) (closure P.region) :=
  ((hw.comp P.regular.continuousOn P.mapsTo).mono P.contains).mul
    (coefficient_continuous P omega h)

theorem weighted_integrable : weighted_integrableType := by
  intro k n O P omega h w hw
  exact continuous_integrable P.jordan (weighted_continuous P omega h w hw)

theorem patch_zero_dimension : patch_zero_dimensionType := by
  intro n O P w f
  change regionIntegral (fun x : P.region => _) = _
  rw [(JordanRegions.zero_dimension P.region).2.2 _ |>.2]
  split_ifs <;> simp [Model.weightedCoefficient, Model.coefficient, pullback_apply, scalarCovector_apply]

theorem seams_contentZero : seams_contentZeroType := by
  intro k s
  exact (LowerDimensionalImages.finite_local_C1_images
    s.dim s.parameter s.map s.lower s.compact s.localC1).2


/-- A common family of smooth ambient weights for any finite patch assembly. -/
theorem ambient_partition_exists : ambient_partition_existsType := by
  intro n K hK ι U hU hcover
  classical
  have ha : ∀ x : K, ∃ a, x.val ∈ U a := by
    intro x
    exact mem_iUnion.mp (hcover x.property)
  choose a ha using ha
  have hb (x : K) := EuclideanSmoothCutoffs.exists_smooth_cutoff
    ({x.val} : Set (E n)) (U (a x)) (isCompact_singleton) (hU _) (by
      intro y hy
      simpa only [mem_singleton_iff.mp hy] using ha x)
  choose rho hrho using hb
  choose V hVo hVsub hVe using fun x => (hrho x).2.2.2.1
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hVo (fun x hx =>
    mem_iUnion.mpr ⟨⟨x,hx⟩, hVsub ⟨x,hx⟩ (mem_singleton x)⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let r : Fin (Fintype.card s) → E n → ℝ := fun i => rho (e i).val
  obtain ⟨w, hw, hn, ht, hsum, hone⟩ := FiniteCompactPartition.normalize_bumps r
    (fun i => (hrho _).1) (fun i x => ((hrho _).2.2.1 x).1)
  have hsupport (i : Fin (Fintype.card s)) : tsupport (w i) ⊆ tsupport (r i) := by
    simpa using ht (id : E n → E n) i
  let W : Set (E n) := ⋃ i : s, V i.val
  have hW : IsOpen W := isOpen_iUnion fun i : s => hVo i.val
  have hKW : K ⊆ W := by simpa only [W, iUnion_subtype] using hs
  have hSW (x : E n) (hx : x ∈ W) : ∑ i, w i x = 1 := by
    apply hone
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hi' : r (e.symm i) x = 1 := by
      simpa only [r, Equiv.apply_symm_apply] using hVe i.val hi
    calc
      1 = r (e.symm i) x := hi'.symm
      _ ≤ ∑ j, r j x := Finset.single_le_sum
        (fun j _ => show 0 ≤ r j x from ((hrho _).2.2.1 x).1) (Finset.mem_univ _)
  refine ⟨Fintype.card s, fun i => a (e i).val,
    ⟨w, hw, hn, ?_, ⟨W,hW,hKW,hSW⟩, fun x => (hsum x).2⟩, ?_⟩
  · intro i
    exact ((hrho _).2.2.2.2.1.of_isClosed_subset
      (isClosed_tsupport _) (hsupport i) : IsCompact (tsupport (w i)))
  · intro i
    exact (hsupport i).trans (hrho _).2.2.2.2.2

lemma contDiff_weighted_local {k n : ℕ} (w : E k → ℝ) (g : E k → E n)
    (U : Set (E k)) (hU : IsOpen U) (hw : ContDiff ℝ 1 w)
    (hg : ContDiffOn ℝ 1 g U) (hs : tsupport w ⊆ U) :
    ContDiff ℝ 1 (fun x => w x • g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hw.contDiffAt.smul ((hg x hx).contDiffAt (hU.mem_nhds hx))
  · have hn : x ∉ tsupport w := fun h => hx (hs h)
    have he : (fun y => w y • g y) =ᶠ[𝓝 x] (fun _ => (0 : E n)) := by
      filter_upwards [(isClosed_tsupport w).isOpen_compl.mem_nhds hn] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem compact_local_extension : compact_local_extensionType := by
  intro k n K h hK hlocal
  classical
  choose U g hU hxU hg heq using fun x : K => hlocal x x.property
  obtain ⟨m, a, P, hsub⟩ := ambient_partition_exists K hK U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩, hxU ⟨x,hx⟩⟩)
  let F : E k → E n := fun x => ∑ i, P.weight i x • g (a i) x
  refine ⟨F, ?_, ?_⟩
  · exact ContDiff.sum fun i _ => contDiff_weighted_local _ _ _ (hU _)
      ((P.smooth i).of_le (by exact_mod_cast le_top)) (hg _) (hsub i)
  · intro x hx
    have hterm (i : Fin m) : P.weight i x • g (a i) x = P.weight i x • h x := by
      by_cases hn : P.weight i x = 0
      · rw [hn, zero_smul, zero_smul]
      · rw [heq _ ⟨hx, hsub i (subset_tsupport _ hn)⟩]
    change (∑ i, P.weight i x • g (a i) x) = h x
    simp_rw [hterm]
    rw [← Finset.sum_smul, P.sum_one.choose_spec.2.2 x (P.sum_one.choose_spec.2.1 hx), one_smul]


lemma region_integral_sum {k : ℕ} {S : Set (E k)} (hS : Jordan S)
    {ι : Type} [Fintype ι] (f : ι → S → ℝ) (hf : ∀ i, RegionIntegrable (f i)) :
    RegionIntegrable (fun x => ∑ i, f i x) ∧
    regionIntegral (fun x => ∑ i, f i x) = ∑ i, regionIntegral (f i) := by
  classical
  let Q := enclosingBox S
  have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
  have hi i : Integrable (zeroExtension (f i)) Q :=
    ((integrable_iff_on_enclosing_box _ hQ).mp (hf i)).2
  have his : Integrable (zeroExtension (fun x => ∑ i, f i x)) Q := by
    rw [Localization.zeroExtension_sum]
    exact Darboux.integrable_sum Finset.univ _ (fun i _ => hi i)
  have hs : RegionIntegrable (fun x => ∑ i, f i x) :=
    (integrable_iff_on_enclosing_box _ hQ).mpr
      ⟨regionBounded_of_box _ hQ his.1, his⟩
  refine ⟨hs, ?_⟩
  rw [integral_eq_on_enclosing_box _ hs hQ his]
  have hv i := integral_eq_on_enclosing_box _ (hf i) hQ (hi i)
  have H := Darboux.integral_sum Finset.univ (fun i => zeroExtension (f i))
    (fun i _ => hi i) (by simpa only [Localization.zeroExtension_sum] using his)
  simpa only [Finset.mem_univ, ↓reduceDIte, ← hv, ← Localization.zeroExtension_sum] using H

lemma patch_integral_weight_sum {k n} {O : Set (E n)} (P : Patch k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega)
    {ι : Type} [Fintype ι] (w : ι → E n → ℝ)
    (hw : ∀ i, ContinuousOn (w i) O) :
    patchIntegral P (fun y => ∑ i, w i y) omega = ∑ i, patchIntegral P (w i) omega := by
  have he : (fun x : P.region => weightedCoefficient P (fun y => ∑ i, w i y) omega x) =
      fun x : P.region => ∑ i, weightedCoefficient P (w i) omega x := by
    funext x
    exact Finset.sum_mul _ _ _
  change regionIntegral _ = _
  rw [he]
  exact (region_integral_sum P.jordan _ (fun i => weighted_integrable P omega h _ (hw i))).2

theorem finite_weight_localization : finite_weight_localizationType := by
  intro k n O P omega h ι _ w v hw hv hone
  rw [← patch_integral_weight_sum P omega h (fun i y => w y * v i y)
    (fun i => hw.mul (hv i))]
  apply congrArg regionIntegral
  funext x
  change w (P.map x) * coefficient P omega x =
    (∑ i, w (P.map x) * v i (P.map x)) * coefficient P omega x
  rw [← Finset.mul_sum, hone x x.property, mul_one]

theorem common_weight_refinement : common_weight_refinementType := by
  intro k n O P omega h m l A B
  have ha (x : E k) (hx : x ∈ P.region) : ∑ i, A.weight i (P.map x) = 1 :=
    A.sum_one.choose_spec.2.2 _
      (A.sum_one.choose_spec.2.1 (mem_image_of_mem _ (subset_closure hx)))
  have hb (x : E k) (hx : x ∈ P.region) : ∑ j, B.weight j (P.map x) = 1 :=
    B.sum_one.choose_spec.2.2 _
      (B.sum_one.choose_spec.2.1 (mem_image_of_mem _ (subset_closure hx)))
  have hrow (i : Fin m) := finite_weight_localization P omega h
    (A.weight i) B.weight (A.smooth i).continuous.continuousOn
    (fun j => (B.smooth j).continuous.continuousOn) hb
  refine ⟨hrow, ?_, ?_⟩
  · intro j
    have H := finite_weight_localization P omega h
      (B.weight j) A.weight (B.smooth j).continuous.continuousOn
      (fun i => (A.smooth i).continuous.continuousOn) ha
    simpa only [mul_comm] using H
  · have H := finite_weight_localization P omega h (fun _ => 1) A.weight
      continuousOn_const (fun i => (A.smooth i).continuous.continuousOn) ha
    simpa only [one_mul, hrow] using H


lemma region_integral_congr_off {k : ℕ} {S : Set (E k)} (hS : Jordan S)
    {f g : S → ℝ} (hf : RegionIntegrable f) (hg : RegionIntegrable g)
    {Z : Set (E k)} (hZ : NullCovers.ContentZero Z)
    (heq : ∀ x : S, x.val ∉ Z → f x = g x) :
    regionIntegral f = regionIntegral g := by
  let Q := enclosingBox S
  have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
  have hfi := ((integrable_iff_on_enclosing_box _ hQ).mp hf).2
  have hgi := ((integrable_iff_on_enclosing_box _ hQ).mp hg).2
  rw [integral_eq_on_enclosing_box _ hf hQ hfi, integral_eq_on_enclosing_box _ hg hQ hgi]
  have hz : ∀ x ∈ carrier Q, x ∉ Z → zeroExtension f x = zeroExtension g x := by
    intro x hx hxn
    by_cases hxS : x ∈ S
    · simpa only [zeroExtension_apply f ⟨x,hxS⟩, zeroExtension_apply g ⟨x,hxS⟩] using heq ⟨x,hxS⟩ hxn
    · rw [zeroExtension_of_not_mem f hxS, zeroExtension_of_not_mem g hxS]
  cases k with
  | zero =>
    change lowerIntegral _ Q = lowerIntegral _ Q
    rw [(Darboux.zero_dimension Q _).2.2.1, (Darboux.zero_dimension Q _).2.2.1]
    apply hz 0 (by intro i; exact Fin.elim0 i)
    intro hx
    apply NullCovers.zero_dim_point_not_null
    apply NullCovers.null_mono (singleton_subset_iff.mpr hx)
    exact NullCovers.contentZero_null hZ
  | succ k =>
    exact ExceptionalSets.integral_eq_of_eq_off_null (Nat.succ_pos _) hfi hgi
      (NullCovers.contentZero_null hZ) hz

lemma region_integral_finite_cover {k : ℕ} {S : Set (E k)} (hS : Jordan S)
    (f : E k → ℝ) (hf : ContinuousOn f (closure S))
    {ι : Type} [Fintype ι] (T : ι → Set (E k)) (hT : ∀ i, Jordan (T i))
    (hsub : ∀ i, T i ⊆ S) (hcover : S = ⋃ i, T i)
    {Z : Set (E k)} (hZ : NullCovers.ContentZero Z)
    (hpair : ∀ i j, i ≠ j → T i ∩ T j ⊆ Z) :
    regionIntegral (fun x : S => f x) =
      ∑ i, regionIntegral (fun x : T i => f x) := by
  classical
  let F : ι → S → ℝ := fun i x => if x.val ∈ T i then f x else 0
  have hfS : RegionIntegrable (fun x : S => f x) := continuous_integrable hS hf
  have hi (i : ι) : RegionIntegrable (fun x : T i => f x) :=
    continuous_integrable (hT i) (hf.mono (closure_mono (hsub i)))
  let Q := enclosingBox S
  have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
  have hQT (i : ι) : Encloses (T i) Q := (closure_mono (hsub i)).trans hQ
  have hF (i : ι) : zeroExtension (F i) = zeroExtension (fun x : T i => f x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [zeroExtension_apply (F i) ⟨x,hx⟩]
      by_cases ht : x ∈ T i
      · rw [zeroExtension_apply _ ⟨x,ht⟩]
        exact ite_eq_left ht
      · rw [zeroExtension_of_not_mem _ ht]
        exact ite_eq_right ht
    · rw [zeroExtension_of_not_mem _ hx,
        zeroExtension_of_not_mem _ (fun ht => hx (hsub i ht))]
  have hFi (i : ι) : RegionIntegrable (F i) := by
    have hbox := ((integrable_iff_on_enclosing_box _ (hQT i)).mp (hi i)).2
    rw [← hF i] at hbox
    exact (integrable_iff_on_enclosing_box _ hQ).mpr
      ⟨regionBounded_of_box _ hQ hbox.1, hbox⟩
  have hval (i : ι) : regionIntegral (F i) = regionIntegral (fun x : T i => f x) := by
    have hbox := ((integrable_iff_on_enclosing_box _ (hQT i)).mp (hi i)).2
    have hboxF := ((integrable_iff_on_enclosing_box _ hQ).mp (hFi i)).2
    rw [integral_eq_on_enclosing_box _ (hFi i) hQ hboxF,
      integral_eq_on_enclosing_box _ (hi i) (hQT i) hbox]
    exact congrArg (fun g => lowerIntegral g Q) (hF i)
  have hsum := region_integral_sum hS F hFi
  calc
    regionIntegral (fun x : S => f x) = regionIntegral (fun x => ∑ i, F i x) := by
      apply region_integral_congr_off hS hfS hsum.1 hZ
      intro x hxZ
      obtain ⟨i, hi⟩ := mem_iUnion.mp (show x.val ∈ ⋃ i, T i by rw [← hcover]; exact x.property)
      rw [Finset.sum_eq_single i]
      · exact (ite_eq_left hi).symm
      · intro j _ hji
        have hj : x.val ∉ T j := fun hj => hxZ (hpair j i hji ⟨hj,hi⟩)
        exact ite_eq_right hj
      · simp
    _ = ∑ i, regionIntegral (F i) := hsum.2
    _ = ∑ i, regionIntegral (fun x : T i => f x) := Finset.sum_congr rfl (fun i _ => hval i)

theorem finite_region_cover : finite_region_coverType := by
  intro k n O P omega h w hw ι _ S hS hsub hcover seams hp
  exact region_integral_finite_cover P.jordan (weightedCoefficient P w omega)
    (weighted_continuous P omega h w hw) S hS hsub hcover
    (seams_contentZero seams) hp


lemma frontier_contentZero {k : ℕ} {S : Set (E k)} (hS : Jordan S) :
    NullCovers.ContentZero (frontier S) := by
  cases k with
  | zero =>
    have he : frontier S = ∅ :=
      (show IsClopen S from ⟨isClosed_discrete _, isOpen_discrete _⟩).frontier_eq
    rw [he]
    exact NullCovers.compact_null_contentZero _ isCompact_empty ExceptionalSets.null_empty
  | succ k => exact (jordan_iff_boundary (Nat.succ_pos _) _ (jordan_bounded hS)).mp hS

lemma coefficient_congr_interior {k n} {O : Set (E n)} (P Q : Patch k O)
    (hPQ : EqOn P.map Q.map P.region) (omega : FormField n k)
    {x : E k} (hx : x ∈ interior P.region) :
    coefficient P omega x = coefficient Q omega x := by
  have he : P.map =ᶠ[𝓝 x] Q.map :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hx) (fun y hy => hPQ (interior_subset hy))
  change omega (P.map x) (fun i => fderiv ℝ P.map x (standardBasis k i)) =
    omega (Q.map x) (fun i => fderiv ℝ Q.map x (standardBasis k i))
  rw [he.eq_of_nhds, he.fderiv_eq]

lemma region_domain_congr {k : ℕ} {S T : Set (E k)} (hST : S = T)
    (f : E k → ℝ) :
    (RegionIntegrable (fun x : S => f x) ↔ RegionIntegrable (fun x : T => f x)) ∧
    regionIntegral (fun x : S => f x) = regionIntegral (fun x : T => f x) := by
  subst T
  exact ⟨Iff.rfl, rfl⟩

theorem representative_independent : representative_independentType := by
  intro k n O P Q hregion hPQ omega h w hw
  have H := region_domain_congr hregion (weightedCoefficient Q w omega)
  have hg := H.1.mpr (weighted_integrable Q omega h w hw)
  apply Eq.trans ?_ H.2
  apply region_integral_congr_off P.jordan (weighted_integrable P omega h w hw) hg
    (frontier_contentZero P.jordan)
  intro x hx
  have hxi : x.val ∈ interior P.region :=
    not_not.mp (fun hxi => hx ⟨subset_closure x.property, hxi⟩)
  change w (P.map x) * coefficient P omega x = w (Q.map x) * coefficient Q omega x
  rw [hPQ x.property, coefficient_congr_interior P Q hPQ omega hxi]

/-- Finite disjoint Jordan localization, with compact containment in each
prescribed open neighborhood. No differentiability of S is asserted. -/
theorem jordan_localization : jordan_localizationType := by
  intro k S hS ι U hU hcover
  classical
  let K := closure S
  have hK : IsCompact K := (jordan_bounded hS).isCompact_closure
  choose a ha using (fun x : K => mem_iUnion.mp (hcover x.property))
  choose B hxB hnd hBU using (fun x : K =>
    OneCoordinate.Boxes.exists_closed_box (hU (a x)) x.val (ha x))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => interior (carrier (B x)))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩, hxB ⟨x,hx⟩⟩)
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let C : Fin (Fintype.card t) → Set (E k) := fun i => S ∩ carrier (B (e i).val)
  let R := disjointed C
  have hC (i : Fin (Fintype.card t)) : Jordan (C i) :=
    jordan_inter hS (OneCoordinate.Boxes.jordan_carrier _)
  have hR (i : Fin (Fintype.card t)) : Jordan (R i) :=
    disjointedRec (p := fun A : Set (E k) => Jordan A)
      (fun {_ j} hj => jordan_diff hj (hC j)) (hC i)
  refine ⟨Fintype.card t, fun i => a (e i).val, R, hR, ?_, ?_,
    disjoint_disjointed C, ?_⟩
  · intro i
    exact (disjointed_subset C i).trans inter_subset_left
  · intro i
    have hc : closure (R i) ⊆ carrier (B (e i).val) :=
      closure_minimal ((disjointed_subset C i).trans inter_subset_right)
        (NullCovers.isClosed_carrier _)
    exact hc.trans (hBU _)
  · change S = ⋃ i, disjointed C i
    rw [iUnion_disjointed]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht (subset_closure hx))
      have hxC : x ∈ C (e.symm ⟨i,hi⟩) := by
        change x ∈ S ∩ carrier (B (e (e.symm ⟨i,hi⟩)).val)
        simpa only [Equiv.apply_symm_apply, mem_inter_iff] using And.intro hx (interior_subset hxi)
      exact mem_iUnion.mpr ⟨e.symm ⟨i,hi⟩, hxC⟩
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hi.1


lemma coefficient_reparam_at {k n : ℕ} {O : Set (E n)} (P Q : Patch k O)
    (e : E k → E k) (omega : FormField n k) (x : E k)
    (hPQ : P.map =ᶠ[𝓝 x] Q.map ∘ e) (he : DifferentiableAt ℝ e x)
    (hQ : DifferentiableAt ℝ Q.map (e x)) :
    coefficient P omega x = coefficient Q omega (e x) * (fderiv ℝ e x).det := by
  have hd : fderiv ℝ P.map x = (fderiv ℝ Q.map (e x)).comp (fderiv ℝ e x) :=
    hPQ.fderiv_eq.trans (fderiv_comp x hQ he)
  have hc : coefficient P omega x =
      pullback e (pullback Q.map omega) x (standardBasis k) := by
    change omega (P.map x) (fun i => fderiv ℝ P.map x (standardBasis k i)) =
      omega (Q.map (e x))
        (fun i => fderiv ℝ Q.map (e x) (fderiv ℝ e x (standardBasis k i)))
    rw [hPQ.eq_of_nhds, hd]
    rfl
  have ht : pullback Q.map omega =
      fun y => coefficient Q omega y • volumeForm k :=
    funext fun y => DirectedSubstitution.topForm_eq_coefficient_smul _
  rw [hc, ht, Orientation.pullback_coefficient]

lemma local_patch_substitution {k n : ℕ} {O : Set (E n)} (P Q : Patch k O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (w : E n → ℝ) (hw : ContinuousOn w O)
    (h : E k → E k) (hh : MapsTo h P.region Q.region)
    (hPQ : EqOn P.map (Q.map ∘ h) P.region)
    (R : Set (E k)) (hR : Jordan R) (hRS : R ⊆ P.region)
    (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hRe : closure R ⊆ e.source)
    (heq : EqOn e h (closure P.region ∩ e.source))
    (sigma : ℝ) (hs : sigma = 1 ∨ sigma = -1)
    (hsign : ∀ x ∈ e.source, Real.sign ((fderiv ℝ e x).det) = sigma) :
    regionIntegral (fun x : R => weightedCoefficient P w omega x) =
      sigma * regionIntegral (fun y : e '' R => weightedCoefficient Q w omega y) := by
  have hTR : e '' R ⊆ Q.region := by
    rintro y ⟨x,hx,rfl⟩
    rw [heq ⟨subset_closure (hRS hx), hRe (subset_closure hx)⟩]
    exact hh (hRS hx)
  have hjT := (RegionSubstitution.jordan_image e he hei R hR
    (jordan_bounded hR).isCompact_closure hRe).2
  let f : e '' R → ℝ := fun y => weightedCoefficient Q w omega y
  have hfi : RegionIntegrable f := continuous_integrable hjT
    ((weighted_continuous Q omega ho w hw).mono (closure_mono hTR))
  let g : R → ℝ := fun x => pullback e
    (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
  have hsub := Orientation.signed_region_substitution e he hei R hR
    (jordan_bounded hR).isCompact_closure hRe sigma hs
    (fun x hx => hsign x (hRe (subset_closure hx))) f hfi.1
  have hgi : RegionIntegrable g := hsub.2.1.mp hfi
  have hp : RegionIntegrable (fun x : R => weightedCoefficient P w omega x) :=
    continuous_integrable hR
      ((weighted_continuous P omega ho w hw).mono (closure_mono hRS))
  have hval : regionIntegral (fun x : R => weightedCoefficient P w omega x) =
      regionIntegral g := by
    apply region_integral_congr_off hR hp hgi (frontier_contentZero P.jordan)
    intro x hxZ
    have hxS : x.val ∈ interior P.region :=
      not_not.mp (fun hxi => hxZ ⟨subset_closure (hRS x.property), hxi⟩)
    have hxe := hRe (subset_closure x.property)
    have hev : e x = h x := heq ⟨subset_closure (hRS x.property), hxe⟩
    have H : P.map =ᶠ[𝓝 x.val] Q.map ∘ e := by
      filter_upwards [isOpen_interior.mem_nhds hxS, e.open_source.mem_nhds hxe] with y hy hye
      exact (hPQ (interior_subset hy)).trans
        (congrArg Q.map (heq ⟨subset_closure (interior_subset hy),hye⟩).symm)
    have heD : DifferentiableAt ℝ e x :=
      ((he x hxe).contDiffAt (e.open_source.mem_nhds hxe)).differentiableAt (by norm_num)
    have hxQ : e x ∈ Q.domain :=
      Q.contains (subset_closure (hTR (mem_image_of_mem e x.property)))
    have hqD : DifferentiableAt ℝ Q.map (e x) :=
      ((Q.regular _ hxQ).contDiffAt (Q.open_domain.mem_nhds hxQ)).differentiableAt (by norm_num)
    have hd := coefficient_reparam_at P Q e omega x H heD hqD
    change w (P.map x) * coefficient P omega x = g x
    dsimp only [g]
    rw [Orientation.pullback_coefficient, zeroExtension_apply f ⟨e x,mem_image_of_mem e x.property⟩]
    change w (P.map x) * coefficient P omega x =
      (w (Q.map (e x)) * coefficient Q omega (e x)) * (fderiv ℝ e x).det
    rw [hd, H.eq_of_nhds]
    simp only [Function.comp_apply, mul_assoc]
  exact hval.trans (hsub.2.2 (Or.inl hfi))

theorem local_reparametrization : local_reparametrizationType := by
  intro k n O P Q sigma hs h hPQ omega ho w hw
  classical
  choose e hxe he hei heq hsign using fun x : closure P.region => h.localCharts x x.property
  obtain ⟨m,a,R,hR,hRS,hRe,hdisj,hcover⟩ := jordan_localization P.region P.jordan
    (fun x : closure P.region => (e x).source) (fun x => (e x).open_source)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxe ⟨x,hx⟩⟩)
  let T : Fin m → Set (E k) := fun i => e (a i) '' R i
  have hT (i : Fin m) : Jordan (T i) :=
    (RegionSubstitution.jordan_image (e (a i)) (he (a i)) (hei (a i)) (R i) (hR i)
      (jordan_bounded (hR i)).isCompact_closure (hRe i)).2
  have hmatch (i : Fin m) {x : E k} (hx : x ∈ R i) : e (a i) x = h.map x :=
    heq (a i) ⟨subset_closure (hRS i hx),hRe i (subset_closure hx)⟩
  have hTQ (i : Fin m) : T i ⊆ Q.region := by
    rintro y ⟨x,hx,rfl⟩
    rw [hmatch i hx]
    exact h.bijective.mapsTo (hRS i hx)
  have hcoverT : Q.region = ⋃ i, T i := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩ := h.bijective.surjOn hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover ▸ hx)
      exact mem_iUnion.mpr ⟨i,x,hi,hmatch i hi⟩
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact hTQ i hi
  have hempty : NullCovers.ContentZero (∅ : Set (E k)) :=
    NullCovers.compact_null_contentZero _ isCompact_empty ExceptionalSets.null_empty
  have hpR : ∀ i j, i ≠ j → R i ∩ R j ⊆ (∅ : Set (E k)) := by
    intro i j hij x hx
    exact (Set.disjoint_left.mp (hdisj hij) hx.1 hx.2).elim
  have hpT : ∀ i j, i ≠ j → T i ∩ T j ⊆ (∅ : Set (E k)) := by
    intro i j hij y hy
    obtain ⟨x,hx,hxy⟩ := hy.1
    obtain ⟨z,hz,hzy⟩ := hy.2
    have hxz : x = z := h.bijective.injOn (hRS i hx) (hRS j hz)
      ((hmatch i hx).symm.trans (hxy.trans (hzy.symm.trans (hmatch j hz))))
    exact (Set.disjoint_left.mp (hdisj hij) hx (hxz.symm ▸ hz)).elim
  have hsrc := region_integral_finite_cover P.jordan (weightedCoefficient P w omega)
    (weighted_continuous P omega ho w hw) R hR hRS hcover hempty hpR
  have htgt := region_integral_finite_cover Q.jordan (weightedCoefficient Q w omega)
    (weighted_continuous Q omega ho w hw) T hT hTQ hcoverT hempty hpT
  change regionIntegral (fun x : P.region => weightedCoefficient P w omega x) =
    sigma * regionIntegral (fun y : Q.region => weightedCoefficient Q w omega y)
  rw [hsrc, htgt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => local_patch_substitution P Q omega ho w hw
    h.map h.bijective.mapsTo hPQ (R i) (hR i) (hRS i) (e (a i))
    (he (a i)) (hei (a i)) (hRe i) (heq (a i)) sigma hs (hsign (a i))

theorem patch_of_local_extensions : patch_of_local_extensionsType := by
  intro k n O hO S h hS hmap hlocal
  obtain ⟨F,hF,hFeq⟩ := compact_local_extension (closure S) h
    (jordan_bounded hS).isCompact_closure hlocal
  refine ⟨{ region := S
            jordan := hS
            map := F
            domain := F ⁻¹' O
            open_domain := hO.preimage hF.continuous
            contains := ?_
            regular := hF.contDiffOn
            mapsTo := fun _ hx => hx },rfl,hFeq⟩
  intro x hx
  change F x ∈ O
  rw [hFeq hx]
  exact hmap hx

lemma integral_weight_congr {k n} {O : Set (E n)} (P : Patch k O)
    (omega : FormField n k) (w v : E n → ℝ) (h : EqOn w v (P.map '' P.region)) :
    patchIntegral P w omega = patchIntegral P v omega := by
  apply congrArg regionIntegral
  funext x
  change w (P.map x) * _ = v (P.map x) * _
  rw [h (mem_image_of_mem P.map x.property)]

theorem matching_reparametrization : matching_reparametrizationType := by
  intro k n O P Q sigma hs h hPQ omega ho w v hw hv hwv
  exact (local_reparametrization P Q sigma hs h hPQ omega ho w hw).trans
    (congrArg (sigma * ·) (integral_weight_congr Q omega w v hwv))

theorem region_coefficient_integral : region_coefficient_integralType := by
  intro k S hS f hf
  have hsupport : support (zeroExtension f) ⊆ S := by
    intro x hx
    by_contra h
    exact hx (zeroExtension_of_not_mem f h)
  have hQ : Encloses S (enclosingBox S) := enclosingBox_encloses (jordan_bounded hS)
  have hi := (region_integrable_iff_box f hQ).mp hf
  have hp : DirectedSubstitution.ProperIntegrable f :=
    ⟨(jordan_bounded hS).subset hsupport, enclosingBox S, (closure_mono hsupport).trans hQ,hi⟩
  obtain ⟨hi',hv⟩ := DirectedSubstitution.proper_on_box hp (enclosingBox S)
    ((closure_mono hsupport).trans hQ)
  exact ⟨hp,(integral_eq_on_enclosing_box f hf hQ hi').trans hv.symm⟩

/-- The closed-box convention and the Jordan convention give the same value.
Subdivision is used to discard only the common faces, rather than treating
closed boxes as strictly enclosed in themselves. -/
lemma box_region_integral {k : ℕ} (Q : Box k) (hQ : Nondegenerate Q)
    (f : E k → ℝ) (hf : ContinuousOn f (carrier Q)) :
    regionIntegral (fun x : carrier Q => f x) = lowerIntegral f Q := by
  classical
  have hj := OneCoordinate.Boxes.jordan_carrier Q
  let F := zeroExtension (fun x : carrier Q => f x)
  have hcont : ContinuousOn f (closure (carrier Q)) := by
    simpa only [(NullCovers.isClosed_carrier Q).closure_eq] using hf
  have hfi := continuous_integrable hj hcont
  let B : Box k := {
    lower := Q.lower - WithLp.toLp 2 (fun _ => 1)
    upper := Q.upper + WithLp.toLp 2 (fun _ => 1)
    ordered := fun i => by
      change Q.lower i - 1 ≤ Q.upper i + 1
      linarith [Q.ordered i] }
  have hB : Encloses (carrier Q) B := by
    change closure (carrier Q) ⊆ interior (carrier B)
    rw [(NullCovers.isClosed_carrier Q).closure_eq, interior_carrier]
    intro x hx i
    change Q.lower i - 1 < x i ∧ x i < Q.upper i + 1
    constructor <;> linarith [(hx i).1,(hx i).2]
  have hiB : Integrable F B := (region_integrable_iff_box _ hB).mp hfi
  let P : Grid B := fun i => threePartition (B.lower i) (Q.lower i) (Q.upper i)
    (B.upper i) (by change Q.lower i - 1 < Q.lower i; linarith) (hQ i)
    (by change Q.upper i < Q.upper i + 1; linarith)
  let c₀ : CellIndex P := fun _ => (1 : Fin 3)
  have hmid : cellBox P c₀ = Q := by
    apply Subdivision.box_ext <;> ext i <;> rfl
  have hci (c : CellIndex P) : Integrable F (cellBox P c) :=
    (subdivision_integrable F B hiB.1 P).mp hiB c
  have hother (c : CellIndex P) (hc : c ≠ c₀) :
      integral F (cellBox P c) (hci c) = 0 := by
    by_cases hk : k = 0
    · subst k
      exact (hc (Subsingleton.elim c c₀)).elim
    have hz : ∀ x ∈ carrier (cellBox P c), x ∉ frontier (carrier Q) → F x = 0 := by
      intro x hxc hxfront
      by_cases hx : x ∈ carrier Q
      · have hxi : x ∈ interior (carrier Q) :=
          not_not.mp (fun hni => hxfront ⟨subset_closure hx,hni⟩)
        rw [interior_carrier] at hxi
        obtain ⟨i,hi⟩ : ∃ i, c i ≠ (1 : Fin 3) := by
          by_contra! he
          exact hc (funext he)
        have hxc' := hxc i
        change ![B.lower i,Q.lower i,Q.upper i,B.upper i] (c i).castSucc ≤ x i ∧
          x i ≤ ![B.lower i,Q.lower i,Q.upper i,B.upper i] (c i).succ at hxc'
        generalize hci' : c i = j at hxc' hi
        fin_cases j
        · norm_num at hxc'
          exact False.elim ((not_lt_of_ge hxc'.2) (hxi i).1)
        · exact (hi rfl).elim
        · norm_num at hxc'
          exact False.elim ((not_lt_of_ge hxc'.1) (hxi i).2)
      · exact zeroExtension_of_not_mem _ hx
    have hv := ExceptionalSets.integral_eq_of_eq_off_null (Nat.pos_of_ne_zero hk)
      (hci c) (integrable_const (cellBox P c) 0)
      (NullCovers.contentZero_null (frontier_contentZero hj)) hz
    exact hv.trans ((constant_integrals _ 0).1.trans (zero_mul _))
  rw [integral_eq_on_enclosing_box _ hfi hB hiB, subdivision_integral F B P hiB hci]
  rw [Finset.sum_eq_single c₀]
  · change lowerIntegral F (cellBox P c₀) = lowerIntegral f Q
    rw [hmid]
    exact lowerIntegral_congr (fun x hx => zeroExtension_apply _ ⟨x,hx⟩)
  · intro c _ hc
    exact hother c hc
  · simp

theorem cell_patch_exists : cell_patch_existsType := by
  intro r k n O c
  obtain ⟨U,hU,hcube,hreg,hmap⟩ := Cells.extension_into_target c
  have hcl : closure (Cells.cube k) = Cells.cube k :=
    (NullCovers.isClosed_carrier _).closure_eq
  let P : Patch k O := {
    region := Cells.cube k
    jordan := OneCoordinate.Boxes.jordan_carrier _
    map := Cells.cellExtension c
    domain := U
    open_domain := hU
    contains := by simpa only [hcl] using hcube
    regular := hreg.of_le (by exact_mod_cast c.positive)
    mapsTo := hmap }
  refine ⟨P,rfl,rfl,?_⟩
  intro omega ho
  change regionIntegral (fun x : carrier (Cells.cubeBox k) =>
    1 * Cells.cellCoefficient c omega x) = _
  simp only [one_mul]
  exact box_region_integral (Cells.cubeBox k) (fun _ => zero_lt_one)
    (Cells.cellCoefficient c omega) (Cells.cellCoefficient_continuous c omega ho)

@[simp] lemma chain_integral_single {k n} {O : Set (E n)} (omega : FormField n k)
    (p : WeightedPatch k O) (a : ℤ) :
    patchChainIntegral omega (Finsupp.single p a) = a • patchIntegral p.patch p.weight omega := by
  exact Finsupp.liftAddHom_apply_single _ p a

theorem geometric_equivalence_sound : geometric_equivalence_soundType := by
  intro k n O omega ho C D h
  induction h with
  | reparam p q s hs h hm hw =>
    have hs' : (s : ℝ) = 1 ∨ (s : ℝ) = -1 := by rcases hs with rfl | rfl <;> norm_num
    simpa using matching_reparametrization p.patch q.patch s hs' h hm omega ho
      p.weight q.weight p.continuous q.continuous hw
  | representative p q hr hm hw =>
    simpa using (representative_independent p.patch q.patch hr hm omega ho
      p.weight p.continuous).trans (integral_weight_congr q.patch omega _ _ hw)
  | cover p m S hS hsub hcover seams hpair =>
    simpa [restrictWeighted] using finite_region_cover p.patch omega ho p.weight p.continuous S hS hsub
      hcover seams hpair
  | localization p m A =>
    obtain ⟨V,hV,hKV,hAV⟩ := A.sum_one
    have hsum : ∀ x ∈ p.patch.region, ∑ i, A.weight i (p.patch.map x) = 1 :=
      fun x hx => hAV _ (hKV (mem_image_of_mem p.patch.map (subset_closure hx)))
    simpa [multiplyWeight] using finite_weight_localization p.patch omega ho p.weight A.weight p.continuous
      (fun i => (A.smooth i).continuous.continuousOn) hsum
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | add h1 h2 ih1 ih2 => simp only [map_add,ih1,ih2]
  | zsmul a h ih => simp only [map_zsmul,ih]

theorem chain_zero_dimension : chain_zero_dimensionType := by
  intro n O C f
  change C.sum (fun p a => a • patchIntegral p.patch p.weight (fun y => scalarCovector (f y))) = _
  apply Finsupp.sum_congr
  intro p a
  exact congrArg (C p • ·) (patch_zero_dimension p.patch p.weight f)

theorem ambient_partition_refinement : ambient_partition_refinementType := by
  intro n K m l A B
  classical
  let e : Fin (m * l) ≃ Fin m × Fin l := finProdFinEquiv.symm
  let w : Fin (m * l) → E n → ℝ := fun r y => A.weight (e r).1 y * B.weight (e r).2 y
  have hsum (y : E n) : ∑ r, w r y = (∑ i, A.weight i y) * (∑ j, B.weight j y) := by
    change (∑ r, (fun ij : Fin m × Fin l => A.weight ij.1 y * B.weight ij.2 y) (e r)) = _
    calc
      _ = ∑ ij : Fin m × Fin l, A.weight ij.1 y * B.weight ij.2 y :=
        e.sum_comp (fun ij => A.weight ij.1 y * B.weight ij.2 y)
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        exact (Finset.sum_mul _ _ _).symm
  obtain ⟨V,hV,hKV,hAV⟩ := A.sum_one
  obtain ⟨W,hW,hKW,hBW⟩ := B.sum_one
  let C : AmbientPartition K (m * l) := {
    weight := w
    smooth := fun r => (A.smooth (e r).1).mul (B.smooth (e r).2)
    nonneg := fun r y => mul_nonneg (A.nonneg _ y) (B.nonneg _ y)
    compact := fun r => (A.compact (e r).1).mul_right
    sum_one := ⟨V ∩ W,hV.inter hW,subset_inter hKV hKW,fun y hy => by
      rw [hsum, hAV y hy.1,hBW y hy.2,mul_one]⟩
    sum_le_one := fun y => by
      rw [hsum]
      calc
        _ ≤ (∑ i, A.weight i y) * 1 := mul_le_mul_of_nonneg_left (B.sum_le_one y)
          (Finset.sum_nonneg (fun i _ => A.nonneg i y))
        _ ≤ 1 := by simpa using A.sum_le_one y }
  refine ⟨C,?_⟩
  intro ij
  have he : e (finProdFinEquiv ij) = ij := finProdFinEquiv.symm_apply_apply ij
  refine ⟨?_,?_⟩
  · change (fun y => A.weight (e (finProdFinEquiv ij)).1 y *
        B.weight (e (finProdFinEquiv ij)).2 y) = _
    rw [he]
  · change tsupport (A.weight (e (finProdFinEquiv ij)).1 *
        B.weight (e (finProdFinEquiv ij)).2) ⊆ _
    rw [he]
    exact subset_inter tsupport_mul_subset_left tsupport_mul_subset_right

theorem finite_patch_partition : finite_patch_partitionType := by
  intro k n O q P ι U hU hcover
  apply ambient_partition_exists _ (isCompact_iUnion (fun j => ?_)) U hU hcover
  exact (region_compact (P j)).image_of_continuousOn
    ((P j).regular.continuousOn.mono (P j).contains)

theorem chart_coefficient_bridge : chart_coefficient_bridgeType := by
  intro k n O P omega ho w hw T f hz
  have hp := region_coefficient_integral P.jordan _ (weighted_integrable P omega ho w hw)
  exact ⟨(DirectedSubstitution.proper_congr hz).1.mpr hp.1,
    ((DirectedSubstitution.proper_congr hz).2).trans hp.2.symm⟩

/-- Gluing relative local representatives preserves values on a relative
neighborhood, and therefore also preserves the upstream chart differential. -/
lemma compact_relative_extension {k n} (K L : Set (E k)) (h : E k → E n)
    (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ (U : Set (E k)) (g : E k → E n),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (L ∩ U)) :
    ∃ (F : E k → E n) (V : Set (E k)), ContDiff ℝ 1 F ∧ IsOpen V ∧
      K ⊆ V ∧ EqOn F h (L ∩ V) := by
  classical
  choose U g hU hxU hg heq using fun x : K => hlocal x x.property
  obtain ⟨m,a,P,hsub⟩ := ambient_partition_exists K hK U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩, hxU ⟨x,hx⟩⟩)
  obtain ⟨V,hV,hKV,hsum⟩ := P.sum_one
  let F : E k → E n := fun x => ∑ i, P.weight i x • g (a i) x
  refine ⟨F,V,?_,hV,hKV,?_⟩
  · exact ContDiff.sum fun i _ => contDiff_weighted_local _ _ _ (hU _)
      ((P.smooth i).of_le (by exact_mod_cast le_top)) (hg _) (hsub i)
  · intro x hx
    have hterm (i : Fin m) : P.weight i x • g (a i) x = P.weight i x • h x := by
      by_cases hn : P.weight i x = 0
      · rw [hn,zero_smul,zero_smul]
      · rw [heq _ ⟨hx.1,hsub i (subset_tsupport _ hn)⟩]
    change (∑ i, P.weight i x • g (a i) x) = h x
    simp_rw [hterm]
    rw [← Finset.sum_smul,hsum x hx.2,one_smul]

theorem chart_patch_exists : chart_patch_existsType := by
  intro r k n M c hr O hO S hS hsource hmap
  have hlocal : ∀ x ∈ closure S, ∃ (U : Set (E k)) (g : E k → E n),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g c.toFun (c.source ∩ U) := by
    intro x hx
    obtain ⟨U,g,hU,hxU,heq,hg,_⟩ := c.regular x (hsource hx)
    exact ⟨U,g,hU,hxU,hg.of_le hr.1,heq⟩
  obtain ⟨F,V,hF,hV,hKV,heq⟩ := compact_relative_extension (closure S) c.source c.toFun
    (jordan_bounded hS).isCompact_closure hlocal
  have hFeq : EqOn F c.toFun (closure S) := fun x hx => heq ⟨hsource hx,hKV hx⟩
  let P : Patch k O := {
    region := S
    jordan := hS
    map := F
    domain := V ∩ F ⁻¹' O
    open_domain := hV.inter (hO.preimage hF.continuous)
    contains := fun x hx => ⟨hKV hx, by change F x ∈ O; rw [hFeq hx]; exact hmap hx⟩
    regular := hF.contDiffOn
    mapsTo := fun _ hx => hx.2 }
  refine ⟨P,rfl,hFeq,?_⟩
  intro x hx
  exact (D04.EmbeddedChart.differential_extension c (hsource hx) hV (hKV hx) heq
    (hF.differentiable (by norm_num) x)).symm

theorem chart_integral_bridge : chart_integral_bridgeType := by
  intro r k n M c O P hsource hmap hd omega ho w hw
  let f : c.source → ℝ := fun u => if u.val ∈ P.region then
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.localizedTopCoefficient
      (ambientRestriction omega) c w u else 0
  apply chart_coefficient_bridge P omega ho w hw c.source f
  funext x
  change zeroExtension f x = zeroExtension (fun x : P.region => weightedCoefficient P w omega x) x
  by_cases hx : x ∈ P.region
  · rw [zeroExtension_apply f ⟨x,hsource hx⟩,zeroExtension_apply _ ⟨x,hx⟩]
    dsimp only [f]
    rw [ite_eq_left hx]
    change w (c.toFun x) * omega (c.toFun x)
      (fun i => chartDifferential c x (standardBasis k i)) =
      w (P.map x) * omega (P.map x) (fun i => fderiv ℝ P.map x (standardBasis k i))
    rw [hmap hx,hd x hx]
  · rw [zeroExtension_of_not_mem _ hx]
    by_cases hc : x ∈ c.source
    · rw [zeroExtension_apply f ⟨x,hc⟩]
      exact ite_eq_right hx
    · exact zeroExtension_of_not_mem f hc

theorem common_region_refinement : common_region_refinementType := by
  intro k n O P omega ho w hw m l S T hS hT hSP hTP hcoverS hcoverT A B hpairS hpairT
  let hC : ∀ i j, Jordan (S i ∩ T j) := fun i j => jordan_inter (hS i) (hT j)
  have hrow (i : Fin m) :
      patchIntegral (restrictPatch P (S i) (hS i) (hSP i)) w omega =
        ∑ j, patchIntegral (restrictPatch P (S i ∩ T j) (hC i j)
          (fun _ hx => hSP i hx.1)) w omega := by
    have hcover : S i = ⋃ j, S i ∩ T j := by
      ext x
      constructor
      · intro hx
        obtain ⟨j,hj⟩ := mem_iUnion.mp (hcoverT ▸ hSP i hx)
        exact mem_iUnion.mpr ⟨j,hx,hj⟩
      · intro hx
        obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        exact hj.1
    exact region_integral_finite_cover (hS i) (weightedCoefficient P w omega)
      ((weighted_continuous P omega ho w hw).mono (closure_mono (hSP i)))
      (fun j => S i ∩ T j) (hC i) (fun _ => inter_subset_left) hcover
      (seams_contentZero B) (fun j q hjq x hx => hpairT j q hjq ⟨hx.1.2,hx.2.2⟩)
  have hcol (j : Fin l) :
      patchIntegral (restrictPatch P (T j) (hT j) (hTP j)) w omega =
        ∑ i, patchIntegral (restrictPatch P (S i ∩ T j) (hC i j)
          (fun _ hx => hSP i hx.1)) w omega := by
    have hcover : T j = ⋃ i, S i ∩ T j := by
      ext x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp (hcoverS ▸ hTP j hx)
        exact mem_iUnion.mpr ⟨i,hi,hx⟩
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact hi.2
    exact region_integral_finite_cover (hT j) (weightedCoefficient P w omega)
      ((weighted_continuous P omega ho w hw).mono (closure_mono (hTP j)))
      (fun i => S i ∩ T j) (fun i => hC i j) (fun _ => inter_subset_right) hcover
      (seams_contentZero A) (fun i q hiq x hx => hpairS i q hiq ⟨hx.1.1,hx.2.1⟩)
  refine ⟨hC,hrow,hcol,?_⟩
  exact (finite_region_cover P omega ho w hw S hS hSP hcoverS A hpairS).trans
    (Finset.sum_congr rfl fun i _ => hrow i)

lemma equivalent_finset_sum {k n} {O : Set (E n)} {ι : Type} (s : Finset ι)
    (C D : ι → PatchChain k O) (h : ∀ i ∈ s, GeometricEquivalent (C i) (D i)) :
    GeometricEquivalent (∑ i ∈ s, C i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GeometricEquivalent.refl (0 : PatchChain k O)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem common_localization : common_localizationType := by
  intro k n O p m l A B
  classical
  let a : Fin m → WeightedPatch k O := fun i =>
    multiplyWeight p (A.weight i) (A.smooth i).continuous.continuousOn
  let b : Fin l → WeightedPatch k O := fun j =>
    multiplyWeight p (B.weight j) (B.smooth j).continuous.continuousOn
  let C : PatchChain k O := ∑ i, ∑ j, Finsupp.single
    (multiplyWeight (a i) (B.weight j) (B.smooth j).continuous.continuousOn) 1
  change GeometricEquivalent (∑ i, Finsupp.single (a i) 1) C ∧
    GeometricEquivalent (∑ j, Finsupp.single (b j) 1) C
  constructor
  · exact equivalent_finset_sum Finset.univ _ _ (fun i _ =>
      GeometricEquivalent.localization (a i) l B)
  · have hcols : GeometricEquivalent (∑ j, Finsupp.single (b j) 1)
        (∑ j, ∑ i, Finsupp.single
          (multiplyWeight (b j) (A.weight i) (A.smooth i).continuous.continuousOn) 1) :=
      equivalent_finset_sum Finset.univ _ _ (fun j _ =>
        GeometricEquivalent.localization (b j) m A)
    apply hcols.trans
    dsimp only [C]
    rw [Finset.sum_comm]
    apply equivalent_finset_sum Finset.univ
    intro i _
    apply equivalent_finset_sum Finset.univ
    intro j _
    apply GeometricEquivalent.representative
      (multiplyWeight (b j) (A.weight i) (A.smooth i).continuous.continuousOn)
      (multiplyWeight (a i) (B.weight j) (B.smooth j).continuous.continuousOn)
      rfl (fun _ _ => rfl)
    intro y _
    change (p.weight y * B.weight j y) * A.weight i y =
      (p.weight y * A.weight i y) * B.weight j y
    ring

end D04.GeometricPatches
