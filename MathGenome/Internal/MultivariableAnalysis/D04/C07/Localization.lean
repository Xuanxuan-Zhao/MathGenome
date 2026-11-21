import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.Localization
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions
import Mathlib.Topology.PartitionOfUnity

/-! Finite continuous localization (`paper.tex`, d04:07:localization).
The cutoffs used here are continuous only. Compact support is on the actual
open domain, and its ambient zero extension is connected to the upstream
Riemann integral. The final theorem accepts local identities on the selected
target sets and their source preimages, then proves the global identity. -/

noncomputable section
open Set Function Topology
open scoped BigOperators
namespace D04.Localization
open JordanRegions

/-- A compact ambient subset contained in V is also compact on the actual domain. -/
lemma compact_preimage_subtype {n : ℕ} {V K : Set (E n)}
    (hK : IsCompact K) (hKV : K ⊆ V) :
    IsCompact ((Subtype.val : V → E n) ⁻¹' K) := by
  apply Topology.IsInducing.subtypeVal.isCompact_preimage' hK
  simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using hKV

theorem finite_decomposition : Specs.D04.C07.Localization.finite_decompositionType := by
  intro n ι V K W hV hK hKV hW hcover f hf hs
  classical
  have hfc : HasCompactSupport f :=
    (compact_preimage_subtype hK hKV).of_isClosed_subset (isClosed_tsupport f) hs
  obtain ⟨s, hsc⟩ := hK.elim_finite_subcover W hW hcover
  have hc : K ⊆ ⋃ i : s, W i := by
    simpa only [iUnion_subtype] using hsc
  obtain ⟨ρ, hρ, _⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hK (fun i : s => W i) (fun i => hW i) (locallyFinite_of_finite _) hc
  refine ⟨s, fun i x => f x * ρ i x, ?_, ?_⟩
  · intro i
    refine ⟨hf.mul ((ρ i).continuous.comp continuous_subtype_val),
      hfc.mono (support_mul_subset_left _ _), ?_⟩
    exact tsupport_mul_subset_right.trans
      ((tsupport_comp_subset_preimage (ρ i) continuous_subtype_val).trans
        (preimage_mono (hρ i)))
  · intro x
    by_cases hx : (x : E n) ∈ K
    · have hsum := ρ.sum_eq_one hx
      have hsum' : ∑ i : s, ρ i x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using hsum
      rw [← Finset.mul_sum, hsum', mul_one]
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      simp [hz]

theorem empty_decomposition : Specs.D04.C07.Localization.empty_decompositionType := by
  intro n V f hs
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  intro x
  have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hs h)
  simpa using hz

lemma zeroExtension_eq_extend {n : ℕ} {V : Set (E n)} (f : V → ℝ) :
    zeroExtension f = (Subtype.val : V → E n).extend f 0 := by
  funext x
  by_cases hx : x ∈ V
  · exact (zeroExtension_apply f ⟨x, hx⟩).trans
      (Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩).symm
  · rw [zeroExtension_of_not_mem f hx, extend_apply' (f := (Subtype.val : V → E n)) f (0 : E n → ℝ) x]
    · rfl
    · rintro ⟨y, rfl⟩
      exact hx y.property

lemma zeroExtension_compact {n : ℕ} {V : Set (E n)} {f : V → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (zeroExtension f) := by
  rw [zeroExtension_eq_extend]
  exact hfc.extend_zero continuous_subtype_val

lemma zeroExtension_tsupport {n : ℕ} {V : Set (E n)} {f : V → ℝ}
    (hfc : HasCompactSupport f) :
    tsupport (zeroExtension f) = Subtype.val '' tsupport f := by
  rw [zeroExtension_eq_extend]
  exact hfc.tsupport_extend_zero continuous_subtype_val Subtype.val_injective

theorem compact_support_integrable :
    Specs.D04.C07.Localization.compact_support_integrableType := by
  intro n V f hV hf hfc
  have hc : Continuous (zeroExtension f) := by
    rw [zeroExtension_eq_extend]
    exact HasCompactSupport.continuous_extend_zero hV hf hfc
  have hb := (zeroExtension_compact hfc).isCompact.isBounded.subset
    (subset_tsupport (zeroExtension f))
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded _).mpr hb
  refine ⟨hc, hV, hb, Q, hQ, ?_⟩
  cases n with
  | zero => exact (Darboux.zero_dimension Q _).2.1
  | succ n => exact ExceptionalSets.integrable_continuous (Nat.succ_pos n) Q _ hc.continuousOn

lemma zeroExtension_sum {n : ℕ} {V : Set (E n)} {ι : Type} [Fintype ι]
    (g : ι → V → ℝ) :
    zeroExtension (fun x => ∑ i, g i x) = fun x => ∑ i, zeroExtension (g i) x := by
  classical
  funext x
  by_cases hx : x ∈ V <;>
    simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]

lemma compact_support_sum {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (g : ι → X → ℝ) (hg : ∀ i, HasCompactSupport (g i)) :
    HasCompactSupport (fun x => ∑ i, g i x) := by
  have he : (∑ i, g i) = (fun x => ∑ i, g i x) := by ext x; simp
  rw [← he]
  exact HasCompactSupport.finset_sum (fun i _ => hg i)

theorem open_integral_sum : Specs.D04.C07.Localization.open_integral_sumType := by
  intro n V ι _ g hV hc hk
  classical
  have hs := compact_support_integrable (fun x => ∑ i, g i x) hV
    (continuous_finsetSum _ (fun i _ => hc i)) (compact_support_sum g hk)
  have hi i := (compact_support_integrable (g i) hV (hc i) (hk i)).2
  let K : Set (E n) := ⋃ i, tsupport (zeroExtension (g i))
  have hK : IsCompact K := isCompact_iUnion (fun i => (zeroExtension_compact (hk i)).isCompact)
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded K).mpr hK.isBounded
  have hqi (i : ι) : Encloses (support (zeroExtension (g i))) Q :=
    (closure_mono ((subset_tsupport _).trans (subset_iUnion (fun i =>
      tsupport (zeroExtension (g i))) i))).trans hQ
  have hqsum : Encloses (support (zeroExtension (fun x => ∑ i, g i x))) Q := by
    apply (closure_mono (show support (zeroExtension (fun x => ∑ i, g i x)) ⊆ K from ?_)).trans hQ
    intro x hx
    by_contra hxK
    apply hx
    rw [zeroExtension_sum]
    apply Finset.sum_eq_zero
    intro i _
    exact image_eq_zero_of_notMem_tsupport (fun h => hxK (mem_iUnion.mpr ⟨i, h⟩))
  obtain ⟨hsi, hsval⟩ := open_integral_eq_on_enclosing_box _ hs.2 Q hqsum
  have hival (i : ι) := open_integral_eq_on_enclosing_box (g i) (hi i) Q (hqi i)
  choose hii hvi using hival
  refine ⟨hs.2, ?_⟩
  change openIntegral (fun x => ∑ i, g i x) = ∑ i, openIntegral (g i)
  rw [hsval]
  have hsum := Darboux.integral_sum Finset.univ (fun i => zeroExtension (g i))
    (fun i _ => hii i) (by simpa only [zeroExtension_sum] using hsi)
  simpa only [Finset.mem_univ, ↓reduceDIte, ← hvi, ← zeroExtension_sum] using hsum

theorem pullback_support : Specs.D04.C07.Localization.pullback_supportType := by
  intro n U V e g W hg hgc hs
  have heq := tsupport_comp_eq_preimage g e
  have hcp : HasCompactSupport (g ∘ e) := by
    rw [HasCompactSupport, heq]
    exact e.isCompact_preimage.mpr hgc
  refine ⟨hg.comp e.continuous, hcp, ?_, hcp.isCompact.image continuous_subtype_val⟩
  rw [heq]
  exact preimage_mono hs

theorem weighted_localization : Specs.D04.C07.Localization.weighted_localizationType := by
  intro n ι U V e J W hU hV hJ hW hcover hlocal f hf hfc
  classical
  let K : Set (E n) := Subtype.val '' tsupport f
  have hK : IsCompact K := hfc.isCompact.image continuous_subtype_val
  have hKV : K ⊆ V := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hsK : tsupport f ⊆ Subtype.val ⁻¹' K := by
    intro x hx; exact ⟨x, hx, rfl⟩
  obtain ⟨s, g, hg, heq⟩ := finite_decomposition V K W hV hK hKV hW
    (hKV.trans hcover) f hf hsK
  have hp i := pullback_support e (g i) (W i) (hg i).1 (hg i).2.1 (hg i).2.2
  have hfp := pullback_support e f univ hf hfc (by simp)
  have hkp : HasCompactSupport (fun x => f (e x) * J x) := hfp.2.1.mul_right
  have hki (i : s) : HasCompactSupport (fun x => g i (e x) * J x) := (hp i).2.1.mul_right
  have hci (i : s) : Continuous (fun x => g i (e x) * J x) := (hp i).1.mul hJ
  have hfg : f = fun x => ∑ i, g i x := funext heq
  have hfgJ : (fun x => f (e x) * J x) = fun x => ∑ i, g i (e x) * J x := by
    funext x
    rw [heq (e x), Finset.sum_mul]
  have hsumV : openIntegral f = ∑ i, openIntegral (g i) := by
    rw [hfg]
    exact (open_integral_sum g hV (fun i => (hg i).1) (fun i => (hg i).2.1)).2
  have hsumU : openIntegral (fun x => f (e x) * J x) =
      ∑ i, openIntegral (fun x => g i (e x) * J x) := by
    rw [hfgJ]
    exact (open_integral_sum _ hU hci hki).2
  refine ⟨(compact_support_integrable f hV hf hfc).2,
    (compact_support_integrable _ hU (hfp.1.mul hJ) hkp).2,
    ?_, s, g, ?_, heq, hsumV, hsumU⟩
  · change openIntegral f = openIntegral (fun x => f (e x) * J x)
    rw [hsumV, hsumU]
    exact Finset.sum_congr rfl fun i _ => hlocal i (g i) (hg i).1 (hg i).2.1 (hg i).2.2
  · intro i
    exact ⟨(hg i).1, (hg i).2.1, (hg i).2.2, (hp i).2.1,
      (hp i).2.2.1, (hp i).2.2.2⟩

theorem c1_localization : Specs.D04.C07.Localization.c1_localizationType := by
  intro n ι U V e φ W hU hV hφ _hφe hW hcover hlocal f hf hfc
  have hJ : Continuous (fun x : U => |(fderiv ℝ φ x).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).domRestrict).abs
  have h := weighted_localization e (fun x : U => |(fderiv ℝ φ x).det|) W
    hU hV hJ hW hcover hlocal f hf hfc
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem open_integral_restrict : Specs.D04.C07.Localization.open_integral_restrictType := by
  intro n V W hWV f hV hW hf hfc hs
  classical
  let g : W → ℝ := fun x => f ⟨x, hWV x.property⟩
  have hg : Continuous g := hf.comp (continuous_subtype_val.subtype_mk _)
  let K : Set (E n) := Subtype.val '' tsupport f
  have hK : IsCompact K := hfc.isCompact.image continuous_subtype_val
  have hKW : K ⊆ W := by rintro _ ⟨x, hx, rfl⟩; exact hs hx
  have hsupp : support g ⊆ Subtype.val ⁻¹' K := by
    intro x hx
    exact ⟨⟨x, hWV x.property⟩, subset_tsupport f hx, rfl⟩
  have hgc : HasCompactSupport g :=
    (compact_preimage_subtype hK hKW).of_isClosed_subset (isClosed_tsupport g)
      (closure_minimal hsupp (hK.isClosed.preimage continuous_subtype_val))
  have hext : zeroExtension g = zeroExtension f := by
    funext x
    by_cases hxW : x ∈ W
    · have hxV := hWV hxW
      simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hxW, hxV, g]
    · by_cases hxV : x ∈ V
      · have hz : f ⟨x, hxV⟩ = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hxW (hs h))
        simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hxW, hxV, hz]
      · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hxW, hxV]
  refine ⟨hg, hgc, (compact_support_integrable g hW hg hgc).2, hext, ?_⟩
  change Darboux.lowerIntegral (zeroExtension g) (enclosingBox (support (zeroExtension g))) =
    Darboux.lowerIntegral (zeroExtension f) (enclosingBox (support (zeroExtension f)))
  rw [hext]

theorem c1_localization_on_cover :
    Specs.D04.C07.Localization.c1_localization_on_coverType := by
  intro n ι U V e φ W hU hV hφ hφe hW hWV hcover hlocal f hf hfc
  have hJ : Continuous (fun x : U => |(fderiv ℝ φ x).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).domRestrict).abs
  apply c1_localization e φ W hU hV hφ hφe hW hcover ?_ f hf hfc
  intro i g hg hgc hs
  let gW : W i → ℝ := fun y => g ⟨y, hWV i y.property⟩
  have hrV := open_integral_restrict (hWV i) g hV (hW i) hg hgc hs
  have hp := pullback_support e g (W i) hg hgc hs
  let F : U → ℝ := fun x => g (e x) * |(fderiv ℝ φ x).det|
  have hF : Continuous F := hp.1.mul hJ
  have hFc : HasCompactSupport F := hp.2.1.mul_right
  have hFs : tsupport F ⊆ Subtype.val ⁻¹' (U ∩ φ ⁻¹' W i) := by
    intro x hx
    refine ⟨x.property, ?_⟩
    change φ x ∈ W i
    rw [hφe x]
    exact hp.2.2.1 (tsupport_mul_subset_left hx)
  have hP : IsOpen (U ∩ φ ⁻¹' W i) :=
    hφ.continuousOn.isOpen_inter_preimage hU (hW i)
  have hrU := open_integral_restrict (inter_subset_left (s := U) (t := φ ⁻¹' W i))
    F hU hP hF hFc hFs
  have heq : (fun x : (U ∩ φ ⁻¹' W i : Set (E n)) => F ⟨x, x.property.1⟩) =
      (fun x : (U ∩ φ ⁻¹' W i : Set (E n)) => gW ⟨φ x, x.property.2⟩ * |(fderiv ℝ φ x).det|) := by
    funext x
    change g (e ⟨x, x.property.1⟩) * _ = g ⟨φ x, hWV i x.property.2⟩ * _
    congr 2
    exact Subtype.ext (hφe ⟨x, x.property.1⟩).symm
  calc
    openIntegral g = openIntegral gW := hrV.2.2.2.2.symm
    _ = openIntegral (fun x : (U ∩ φ ⁻¹' W i : Set (E n)) =>
      gW ⟨φ x, x.property.2⟩ * |(fderiv ℝ φ x).det|) := hlocal i gW hrV.1 hrV.2.1
    _ = openIntegral F := by rw [← heq]; exact hrU.2.2.2.2

end D04.Localization
