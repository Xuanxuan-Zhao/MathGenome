import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RiemannSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C07.ContinuousSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C07.NullPreservation
import MathGenome.Internal.MultivariableAnalysis.D04.C07.ContinuousSandwich

noncomputable section
open Set Function Filter Topology
namespace D04.RiemannSubstitution
open Darboux JordanRegions NullCovers DiscontinuityCriterion

variable {n : ℕ} {U V : Set (E n)}

/-- No continuity of f is needed for compactness of its pulled-back support. -/
lemma compact_pullback (e : U ≃ₜ V) {f : V → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (f ∘ e) := by
  rw [HasCompactSupport, tsupport_comp_eq_preimage f e]
  exact e.isCompact_preimage.mpr hf

lemma weighted_bounded (e : U ≃ₜ V) {f : V → ℝ}
    (hb : RegionBounded f) (hk : HasCompactSupport f)
    {J : U → ℝ} (hJ : Continuous J) :
    RegionBounded (fun x => f (e x) * J x) := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨C, hC⟩ := (compact_pullback e hk).exists_bound_of_continuousOn hJ.continuousOn
  refine ⟨max M 0 * max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (f ∘ e)
  · rw [norm_mul]
    exact mul_le_mul (le_max_of_le_left (hM _)) (le_max_of_le_left (hC x hx))
      (norm_nonneg _) (le_max_of_le_right (le_refl 0))
  · have hz : f (e x) = 0 := image_eq_zero_of_notMem_tsupport (f := f ∘ e) hx
    simp only [hz, zero_mul, norm_zero]
    exact mul_nonneg (le_max_right _ _) (le_max_right _ _)

lemma zeroExtension_support_in_domain {f : U → ℝ} (hk : HasCompactSupport f) :
    HasCompactSupport (zeroExtension f) ∧ tsupport (zeroExtension f) ⊆ U := by
  refine ⟨Localization.zeroExtension_compact hk, ?_⟩
  rw [Localization.zeroExtension_tsupport hk]
  rintro _ ⟨x, _, rfl⟩
  exact x.property

lemma continuousAt_off_tsupport {X : Type} [TopologicalSpace X] (F : X → ℝ)
    {x : X} (hx : x ∉ tsupport F) : ContinuousAt F x := by
  apply (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) x).congr
  filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hx] with y hy
  exact (image_eq_zero_of_notMem_tsupport hy).symm

/-- The ambient discontinuity set of a compact-supported zero extension is
null when its Darboux integral exists. Compact containment removes box faces. -/
lemma null_ambient_discontinuities (hn : 0 < n) {f : V → ℝ}
    (hi : OpenIntegrable f) : Null {x | ¬ ContinuousAt (zeroExtension f) x} := by
  obtain ⟨Q, hQ, hfi⟩ := hi.2.2
  have hnull := (integrable_iff_null_discontinuitySet hn _ Q hfi.1).mp hfi
  apply null_mono (T := discontinuitySet (zeroExtension f) Q) _ hnull
  intro x hx
  have hxK : x ∈ tsupport (zeroExtension f) := by
    by_contra h
    exact hx (continuousAt_off_tsupport _ h)
  have hxint : x ∈ interior (carrier Q) := hQ hxK
  refine ⟨interior_subset hxint, fun hc => hx ?_⟩
  exact hc.continuousAt (mem_interior_iff_mem_nhds.mp hxint)

lemma open_integrable_of_null_ambient (hn : 0 < n) {f : U → ℝ}
    (hU : IsOpen U) (hb : RegionBounded f) (hk : HasCompactSupport f)
    (hd : Null {x | ¬ ContinuousAt (zeroExtension f) x}) : OpenIntegrable f := by
  have hs := (Localization.zeroExtension_compact hk).isCompact.isBounded.subset
    (subset_tsupport (zeroExtension f))
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded _).mpr hs
  refine ⟨hU, hs, Q, hQ, ?_⟩
  apply (integrable_iff_null_discontinuitySet hn _ Q (zeroExtension_bounded f hb Q)).mpr
  apply null_mono (T := {x | ¬ ContinuousAt (zeroExtension f) x}) _ hd
  intro x hx hc
  exact hx.2 hc.continuousWithinAt

/-- Integrability transfers before any equality of integrals is used. -/
lemma integrable_pullback (hn : 0 < n) (e : U ≃ₜ V) (φ ψ : E n → E n)
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ 1 φ U)
    (hψ : ContDiffOn ℝ 1 ψ V) (he : ∀ x : U, φ x = e x)
    (heinv : ∀ y : V, ψ y = e.symm y)
    (f : V → ℝ) (hb : RegionBounded f) (hk : HasCompactSupport f)
    (hi : OpenIntegrable f) :
    OpenIntegrable (fun x : U => f (e x) * |(fderiv ℝ φ x).det|) := by
  let J : U → ℝ := fun x => |(fderiv ℝ φ x).det|
  have hJ : Continuous J := (ContinuousLinearMap.continuous_det.comp
    (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).domRestrict).abs
  have hgc : HasCompactSupport (fun x : U => f (e x) * J x) :=
    (compact_pullback e hk).mul_right
  apply open_integrable_of_null_ambient hn hU (weighted_bounded e hb hk hJ) hgc
  let D : Set (E n) := {y | y ∈ V ∧ ¬ ContinuousAt (zeroExtension f) y}
  have hD : Null D := null_mono inter_subset_right (null_ambient_discontinuities hn hi)
  have hψcr := (D04.crOn_iff_contDiffOn 1 V ψ hV).mpr hψ
  have hnull := NullPreservation.c1_null_image hn V ψ hV hψcr D inter_subset_left hD
  apply null_mono (T := ψ '' D) _ hnull
  intro x hx
  have hxK : x ∈ tsupport (zeroExtension (fun x : U => f (e x) * J x)) := by
    by_contra h
    exact hx (continuousAt_off_tsupport _ h)
  have hxU := (zeroExtension_support_in_domain hgc).2 hxK
  let xu : U := ⟨x, hxU⟩
  refine ⟨(e xu : E n), ⟨(e xu).property, ?_⟩, ?_⟩
  · intro hc
    have hcf : ContinuousAt f (e xu) :=
      (region_continuity_iff f (e xu)).mp hc.continuousWithinAt
    have hcg : ContinuousAt (fun x : U => f (e x) * J x) xu :=
      (hcf.comp e.continuous.continuousAt).mul hJ.continuousAt
    exact hx (((region_continuity_iff _ xu).mpr hcg).continuousAt (hU.mem_nhds hxU))
  · simpa only [Homeomorph.symm_apply_apply] using heinv (e xu)

/-- Pointwise order for the shared open-domain Riemann integral. -/
lemma openIntegral_mono {f g : U → ℝ} (hf : OpenIntegrable f) (hg : OpenIntegrable g)
    (hle : ∀ x, f x ≤ g x) : openIntegral f ≤ openIntegral g := by
  let K := support (zeroExtension f) ∪ support (zeroExtension g)
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded K).mpr (hf.2.1.union hg.2.1)
  obtain ⟨hfi, hfv⟩ := open_integral_eq_on_enclosing_box f hf Q
    ((closure_mono subset_union_left).trans hQ)
  obtain ⟨hgi, hgv⟩ := open_integral_eq_on_enclosing_box g hg Q
    ((closure_mono subset_union_right).trans hQ)
  rw [hfv, hgv]
  apply Darboux.integral_mono hfi hgi
  intro x _
  by_cases hx : x ∈ U
  · simpa only [zeroExtension_apply f ⟨x, hx⟩, zeroExtension_apply g ⟨x, hx⟩]
      using hle ⟨x, hx⟩
  · rw [zeroExtension_of_not_mem f hx, zeroExtension_of_not_mem g hx]

lemma zeroExtension_sub (f g : U → ℝ) :
    zeroExtension (fun x => f x - g x) = fun x => zeroExtension f x - zeroExtension g x := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [zeroExtension_apply _ ⟨x, hx⟩]
  · simp only [zeroExtension_of_not_mem _ hx, sub_self]

lemma openIntegral_sub {f g : U → ℝ} (hf : OpenIntegrable f) (hg : OpenIntegrable g)
    (hs : OpenIntegrable (fun x => f x - g x)) :
    openIntegral (fun x => f x - g x) = openIntegral f - openIntegral g := by
  let K := (support (zeroExtension f) ∪ support (zeroExtension g)) ∪
    support (zeroExtension (fun x => f x - g x))
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded K).mpr
    ((hf.2.1.union hg.2.1).union hs.2.1)
  obtain ⟨hfi, hfv⟩ := open_integral_eq_on_enclosing_box f hf Q
    ((closure_mono (subset_union_left.trans subset_union_left)).trans hQ)
  obtain ⟨hgi, hgv⟩ := open_integral_eq_on_enclosing_box g hg Q
    ((closure_mono (subset_union_right.trans subset_union_left)).trans hQ)
  obtain ⟨hsi, hsv⟩ := open_integral_eq_on_enclosing_box _ hs Q
    ((closure_mono subset_union_right).trans hQ)
  rw [hfv, hgv, hsv]
  have he : zeroExtension (fun x => f x - g x) =
      fun x => zeroExtension f x + (-1) * zeroExtension g x := by
    rw [zeroExtension_sub]; funext x; ring
  have hni := Darboux.integrable_smul (-1) hgi
  have hv := Darboux.integral_add hfi hni (he ▸ hsi)
  rw [Darboux.integral_smul (-1) hgi hni] at hv
  change lowerIntegral _ Q = _ at hv ⊢
  rw [he, hv]
  ring

/-- Differentiate the genuine inverse identity, then take absolute determinants.
This proves the nonvanishing needed by continuous substitution as well. -/
lemma inverse_jacobian (e : U ≃ₜ V) (φ ψ : E n → E n)
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ 1 φ U)
    (hψ : ContDiffOn ℝ 1 ψ V) (he : ∀ x : U, φ x = e x)
    (heinv : ∀ y : V, ψ y = e.symm y) (x : U) :
    |(fderiv ℝ ψ (e x)).det| * |(fderiv ℝ φ x).det| = 1 := by
  have hφx : φ x ∈ V := he x ▸ (e x).property
  have hdφ := (hφ.contDiffAt (hU.mem_nhds x.property)).differentiableAt (by norm_num)
  have hdψ := (hψ.contDiffAt (hV.mem_nhds hφx)).differentiableAt (by norm_num)
  have heq : (ψ ∘ φ) =ᶠ[𝓝 (x : E n)] id := by
    filter_upwards [hU.mem_nhds x.property] with z hz
    change ψ (φ z) = z
    rw [he ⟨z, hz⟩, heinv (e ⟨z, hz⟩)]
    simp
  have hder : (fderiv ℝ ψ (φ x)).comp (fderiv ℝ φ x) =
      ContinuousLinearMap.id ℝ (E n) :=
    ((hdψ.hasFDerivAt.comp (x : E n) hdφ.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique
      (hasFDerivAt_id (x : E n))
  have hdet := congrArg ContinuousLinearMap.det hder
  change LinearMap.det (((fderiv ℝ ψ (φ x)) : E n →ₗ[ℝ] E n).comp
    ((fderiv ℝ φ x) : E n →ₗ[ℝ] E n)) =
    LinearMap.det (LinearMap.id : E n →ₗ[ℝ] E n) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  rw [← he x, ← abs_mul, hdet, abs_one]

lemma jacobian_ne_zero (e : U ≃ₜ V) (φ ψ : E n → E n)
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ 1 φ U)
    (hψ : ContDiffOn ℝ 1 ψ V) (he : ∀ x : U, φ x = e x)
    (heinv : ∀ y : V, ψ y = e.symm y) :
    ∀ x ∈ U, (fderiv ℝ φ x).det ≠ 0 := by
  intro x hx hz
  have h := inverse_jacobian e φ ψ hU hV hφ hψ he heinv ⟨x, hx⟩
  rw [hz, abs_zero, mul_zero] at h
  exact zero_ne_one h

lemma compact_restrict {F : E n → ℝ} (hk : HasCompactSupport F)
    (hs : tsupport F ⊆ V) : HasCompactSupport (fun x : V => F x) := by
  apply (Localization.compact_preimage_subtype hk hs).of_isClosed_subset
    (isClosed_tsupport _)
  exact tsupport_comp_subset_preimage F continuous_subtype_val

/-- The continuous pointwise sandwich traps both Riemann integrals in the
same real interval of arbitrarily small length. -/
lemma substitution_forward (hn : 0 < n) (e : U ≃ₜ V) (φ ψ : E n → E n)
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ 1 φ U)
    (hψ : ContDiffOn ℝ 1 ψ V) (he : ∀ x : U, φ x = e x)
    (heinv : ∀ y : V, ψ y = e.symm y)
    (f : V → ℝ) (hb : RegionBounded f) (hk : HasCompactSupport f)
    (hi : OpenIntegrable f) :
    OpenIntegrable (fun x : U => f (e x) * |(fderiv ℝ φ x).det|) ∧
      openIntegral f = openIntegral (fun x : U => f (e x) * |(fderiv ℝ φ x).det|) := by
  let g : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
  have hgi : OpenIntegrable g := integrable_pullback hn e φ ψ hU hV hφ hψ he heinv f hb hk hi
  refine ⟨hgi, ?_⟩
  have hdet := jacobian_ne_zero e φ ψ hU hV hφ hψ he heinv
  apply eq_of_abs_sub_lt_all
  intro ε hε
  obtain ⟨l, u, hl, hu, hlk, huk, hlV, huV, hle, hli, hui, hdi, hgap⟩ :=
    ContinuousSandwich.continuous_sandwich V (tsupport (zeroExtension f)) (zeroExtension f)
      hV (Localization.zeroExtension_compact hk) (zeroExtension_support_in_domain hk).2
      Subset.rfl hi.2.2 ε hε
  let fl : V → ℝ := fun x => l x
  let fu : V → ℝ := fun x => u x
  have hlsub := ContinuousSubstitution.scalar_substitution e φ hn hU hV hφ he hdet
    fl (hl.comp continuous_subtype_val) (compact_restrict hlk hlV)
  have husub := ContinuousSubstitution.scalar_substitution e φ hn hU hV hφ he hdet
    fu (hu.comp continuous_subtype_val) (compact_restrict huk huV)
  have hfl : openIntegral fl ≤ openIntegral f := openIntegral_mono hli hi (fun x => by
    simpa only [fl, zeroExtension_apply f x] using (hle x).1)
  have hfu : openIntegral f ≤ openIntegral fu := openIntegral_mono hi hui (fun x => by
    simpa only [fu, zeroExtension_apply f x] using (hle x).2)
  have hgl : openIntegral fl ≤ openIntegral g := by
    calc
      _ = openIntegral (fun x : U => fl (e x) * |(fderiv ℝ φ x).det|) := hlsub.2.2.2.2.2.2
      _ ≤ _ := openIntegral_mono hlsub.2.2.2.2.2.1 hgi (fun x =>
        mul_le_mul_of_nonneg_right (by
          simpa only [fl, zeroExtension_apply f (e x)] using (hle (e x)).1) (abs_nonneg _))
  have hgu : openIntegral g ≤ openIntegral fu := by
    calc
      _ ≤ openIntegral (fun x : U => fu (e x) * |(fderiv ℝ φ x).det|) :=
        openIntegral_mono hgi husub.2.2.2.2.2.1 (fun x =>
          mul_le_mul_of_nonneg_right (by
            simpa only [fu, zeroExtension_apply f (e x)] using (hle (e x)).2) (abs_nonneg _))
      _ = _ := husub.2.2.2.2.2.2.symm
  have hgap' : openIntegral fu - openIntegral fl < ε := by
    rw [← openIntegral_sub hui hli hdi]
    exact hgap
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem zero_dimension : Specs.D04.C07.RiemannSubstitution.zero_dimensionType := by
  intro U V e φ hU hV f
  let g : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
  have hd (x : E 0) : (fderiv ℝ φ x).det = 1 := LinearMap.det_eq_one_of_subsingleton _
  have hfk : HasCompactSupport f := (Set.toFinite _).isCompact
  have hgk : HasCompactSupport g := (Set.toFinite _).isCompact
  have hfi := (Localization.compact_support_integrable f hV continuous_of_discreteTopology hfk).2
  have hgi := (Localization.compact_support_integrable g hU continuous_of_discreteTopology hgk).2
  have hfv : openIntegral f = zeroExtension f 0 :=
    (Darboux.zero_dimension _ _).2.2.1
  have hgv : openIntegral g = zeroExtension g 0 :=
    (Darboux.zero_dimension _ _).2.2.1
  suffices hz : zeroExtension f 0 = zeroExtension g 0 from
    ⟨hd, hfi, hgi, hfv, hgv, hfv.trans (hz.trans hgv.symm)⟩
  by_cases hy : (0 : E 0) ∈ V
  · have hx : (0 : E 0) ∈ U := by
      have h := (e.symm ⟨0, hy⟩).property
      simpa only [Subsingleton.elim (e.symm ⟨0, hy⟩ : E 0) 0] using h
    rw [zeroExtension_apply f ⟨0, hy⟩, zeroExtension_apply g ⟨0, hx⟩]
    change f ⟨0, hy⟩ = f (e ⟨0, hx⟩) * |(fderiv ℝ φ 0).det|
    rw [hd, abs_one, mul_one]
    congr 1
    exact Subsingleton.elim _ _
  · have hx : (0 : E 0) ∉ U := by
      intro hx
      have h := (e ⟨0, hx⟩).property
      exact hy (by simpa only [Subsingleton.elim (e ⟨0, hx⟩ : E 0) 0] using h)
    rw [zeroExtension_of_not_mem f hy, zeroExtension_of_not_mem g hx]

theorem riemann_substitution : Specs.D04.C07.RiemannSubstitution.riemann_substitutionType := by
  intro n U V e φ ψ hU hV hφ hψ he heinv f hb hk
  let g : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
  have hJ : Continuous (fun x : U => |(fderiv ℝ φ x).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).domRestrict).abs
  have hgb : RegionBounded g := weighted_bounded e hb hk hJ
  have hgk : HasCompactSupport g := (compact_pullback e hk).mul_right
  have hext := zeroExtension_support_in_domain hgk
  refine ⟨hgb, hgk, hext.1, hext.2, ?_, ?_⟩
  · cases n with
    | zero =>
      have hz := zero_dimension e φ hU hV f
      exact ⟨fun _ => hz.2.2.1, fun _ => hz.2.1⟩
    | succ n =>
      constructor
      · exact fun hi => (substitution_forward (Nat.succ_pos n) e φ ψ hU hV hφ hψ he heinv f hb hk hi).1
      · intro hgi
        have hrev := substitution_forward (Nat.succ_pos n) e.symm ψ φ hV hU hψ hφ heinv he g hgb hgk hgi
        have heq : (fun y : V => g (e.symm y) * |(fderiv ℝ ψ y).det|) = f := by
          funext y
          have hprod := inverse_jacobian e φ ψ hU hV hφ hψ he heinv (e.symm y)
          simp only [Homeomorph.apply_symm_apply] at hprod
          change (f (e (e.symm y)) * |(fderiv ℝ φ (e.symm y)).det|) *
            |(fderiv ℝ ψ y).det| = f y
          rw [Homeomorph.apply_symm_apply]
          calc
            _ = f y * (|(fderiv ℝ ψ y).det| * |(fderiv ℝ φ (e.symm y)).det|) := by ring
            _ = f y := by rw [hprod, mul_one]
        rw [heq] at hrev
        exact hrev.1
  · intro hi
    cases n with
    | zero => exact (zero_dimension e φ hU hV f).2.2.2.2.2
    | succ n =>
      rcases hi with hfi | hgi
      · exact (substitution_forward (Nat.succ_pos n) e φ ψ hU hV hφ hψ he heinv f hb hk hfi).2
      · have hrev := substitution_forward (Nat.succ_pos n) e.symm ψ φ hV hU hψ hφ heinv he g hgb hgk hgi
        have heq : (fun y : V => g (e.symm y) * |(fderiv ℝ ψ y).det|) = f := by
          funext y
          have hprod := inverse_jacobian e φ ψ hU hV hφ hψ he heinv (e.symm y)
          simp only [Homeomorph.apply_symm_apply] at hprod
          change (f (e (e.symm y)) * |(fderiv ℝ φ (e.symm y)).det|) *
            |(fderiv ℝ ψ y).det| = f y
          rw [Homeomorph.apply_symm_apply]
          calc
            _ = f y * (|(fderiv ℝ ψ y).det| * |(fderiv ℝ φ (e.symm y)).det|) := by ring
            _ = f y := by rw [hprod, mul_one]
        rw [heq] at hrev
        exact hrev.2.symm

end D04.RiemannSubstitution
