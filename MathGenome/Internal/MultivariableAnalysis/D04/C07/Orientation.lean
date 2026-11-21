import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.Orientation
import MathGenome.Internal.MultivariableAnalysis.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C01.Connectedness
import MathGenome.Internal.MultivariableAnalysis.D04.C13.PullbackCalculus

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Function Topology
namespace D04.Orientation
open Darboux JordanRegions

variable {n : ℕ}

theorem determinant_regular : Specs.D04.C07.Orientation.determinant_regularType := by
  intro n e he hei
  exact ⟨ContinuousLinearMap.continuous_det.comp_continuousOn
    (he.continuousOn_fderiv_of_isOpen e.open_source le_rfl),
    RiemannSubstitution.jacobian_ne_zero e.toHomeomorphSourceTarget e e.symm
      e.open_source e.open_target he hei (fun _ => rfl) (fun _ => rfl)⟩

/-- A continuous real function avoiding zero cannot cross from one half-line
to the other on a preconnected set. -/
lemma constant_sign {X : Type*} [TopologicalSpace X] {C : Set X} {d : X → ℝ}
    (hC : IsPreconnected C) (hd : ContinuousOn d C) (hn : ∀ x ∈ C, d x ≠ 0)
    {a : X} (ha : a ∈ C) :
    (∀ x ∈ C, 0 < d x) ∨ (∀ x ∈ C, d x < 0) := by
  rcases (hn a ha).lt_or_gt with ha' | ha'
  · right
    intro x hx
    by_contra h
    have hx' : 0 < d x := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hn x hx))
    obtain ⟨y, hy, hdy⟩ := hC.intermediate_value ha hx hd ⟨ha'.le, hx'.le⟩
    exact hn y hy hdy
  · left
    intro x hx
    by_contra h
    have hx' : d x < 0 := lt_of_le_of_ne (not_lt.mp h) (hn x hx)
    obtain ⟨y, hy, hdy⟩ := hC.intermediate_value hx ha hd ⟨hx'.le, ha'.le⟩
    exact hn y hy hdy

theorem component_sign : Specs.D04.C07.Orientation.component_signType := by
  intro n e he hei a ha
  obtain ⟨hc, hn⟩ := determinant_regular e he hei
  have hs := constant_sign isPreconnected_connectedComponentIn
    (hc.mono (connectedComponentIn_subset e.source a))
    (fun x hx => hn x (connectedComponentIn_subset e.source a hx))
    (mem_connectedComponentIn ha)
  refine ⟨(Real.sign_apply_eq_of_ne_zero _ (hn a ha)).symm, ?_, hs⟩
  rcases hs with hp | hm
  · intro x hx
    rw [Real.sign_of_pos (hp x hx), Real.sign_of_pos (hp a (mem_connectedComponentIn ha))]
  · intro x hx
    rw [Real.sign_of_neg (hm x hx), Real.sign_of_neg (hm a (mem_connectedComponentIn ha))]

lemma jacobian_det (φ : E n → E n) (x : E n) :
    Matrix.det (jacobian φ x) = (fderiv ℝ φ x).det := by
  change Matrix.det ((matrixLinearEquiv n n).symm (fderiv ℝ φ x).toLinearMap) = _
  exact LinearMap.det_toMatrix (standardBasis n) _

theorem pullback_top : Specs.D04.C07.Orientation.pullback_topType := by
  intro n φ f x
  simpa only [jacobian_det] using D04.pullback_volume φ f x

@[simp] lemma volumeForm_basis : volumeForm n (standardBasis n) = 1 := by
  rw [volumeForm_apply]
  have hm : (fun i j => standardBasis n j i) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [standardBasis_apply, Matrix.one_apply]
  rw [hm, Matrix.det_one]

lemma pullback_coefficient (φ : E n → E n) (f : E n → ℝ) (x : E n) :
    pullback φ (fun y => f y • volumeForm n) x (standardBasis n) =
      f (φ x) * (fderiv ℝ φ x).det := by
  have h : pullback φ (fun y => f y • volumeForm n) x =
      (f (φ x) * (fderiv ℝ φ x).det) • volumeForm n := pullback_top φ f x
  exact (congrArg (fun ω : Covector (E n) n => ω (standardBasis n)) h).trans
    (by simp only [smul_apply, smul_eq_mul, volumeForm_basis, mul_one])

theorem zero_dimension : Specs.D04.C07.Orientation.zero_dimensionType := by
  intro φ x
  have hd : (fderiv ℝ φ x).det = 1 := LinearMap.det_eq_one_of_subsingleton _
  refine ⟨hd, fun f => ?_⟩
  exact (pullback_coefficient φ f x).trans (by rw [hd, mul_one])

lemma zeroExtension_smul {S : Set (E n)} (c : ℝ) (f : S → ℝ) :
    zeroExtension (fun x => c * f x) = fun x => c * zeroExtension f x := by
  funext x
  by_cases hx : x ∈ S
  · simp only [zeroExtension_apply _ ⟨x, hx⟩]
  · simp only [zeroExtension_of_not_mem _ hx, mul_zero]

lemma support_smul_subset {S : Set (E n)} (c : ℝ) (f : S → ℝ) :
    support (zeroExtension (fun x => c * f x)) ⊆ support (zeroExtension f) := by
  rw [zeroExtension_smul]
  intro x hx hf
  exact hx (by simp only [hf, mul_zero])

lemma regionBounded_smul {S : Set (E n)} (c : ℝ) {f : S → ℝ}
    (hf : RegionBounded f) : RegionBounded (fun x => c * f x) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨‖c‖ * M, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg c)

/-- Linearity for the actual zero-extension Riemann integral. The support
may shrink when the scalar is zero, so both enclosing boxes are compared. -/
lemma openIntegral_smul {U : Set (E n)} (c : ℝ) {f : U → ℝ}
    (hf : OpenIntegrable f) :
    OpenIntegrable (fun x => c * f x) ∧
      openIntegral (fun x => c * f x) = c * openIntegral f := by
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded _).mpr hf.2.1
  obtain ⟨hi, hv⟩ := open_integral_eq_on_enclosing_box f hf Q hQ
  have hs := support_smul_subset c f
  have hQc : Encloses (support (zeroExtension (fun x => c * f x))) Q :=
    (closure_mono hs).trans hQ
  have hic : Integrable (zeroExtension (fun x => c * f x)) Q := by
    rw [zeroExtension_smul]
    exact integrable_smul c hi
  have hfc : OpenIntegrable (fun x => c * f x) :=
    ⟨hf.1, hf.2.1.subset hs, Q, hQc, hic⟩
  obtain ⟨hic', hvc⟩ := open_integral_eq_on_enclosing_box _ hfc Q hQc
  refine ⟨hfc, ?_⟩
  rw [hvc, hv]
  simpa only [zeroExtension_smul] using integral_smul c hi (integrable_smul c hi)

lemma regionIntegral_smul {S : Set (E n)} (c : ℝ) {f : S → ℝ}
    (hf : RegionIntegrable f) :
    RegionIntegrable (fun x => c * f x) ∧
      regionIntegral (fun x => c * f x) = c * regionIntegral f := by
  obtain ⟨Q, hQ, hi⟩ := hf.2
  have hic : Integrable (zeroExtension (fun x => c * f x)) Q := by
    rw [zeroExtension_smul]
    exact integrable_smul c hi
  have hfc : RegionIntegrable (fun x => c * f x) :=
    ⟨regionBounded_smul c hf.1, Q, hQ, hic⟩
  refine ⟨hfc, ?_⟩
  rw [integral_eq_on_enclosing_box _ hfc hQ hic,
    integral_eq_on_enclosing_box _ hf hQ hi]
  simpa only [zeroExtension_smul] using integral_smul c hi (integrable_smul c hi)

lemma sign_involution {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) : σ * (σ * t) = t := by
  rcases hσ with rfl | rfl <;> simp

lemma openIntegrable_sign_iff {U : Set (E n)} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (f : U → ℝ) : OpenIntegrable f ↔ OpenIntegrable (fun x => σ * f x) := by
  constructor
  · intro hf; exact (openIntegral_smul σ hf).1
  · intro hf
    simpa only [sign_involution hσ] using (openIntegral_smul σ hf).1

lemma regionIntegrable_sign_iff {S : Set (E n)} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (f : S → ℝ) : RegionIntegrable f ↔ RegionIntegrable (fun x => σ * f x) := by
  constructor
  · intro hf; exact (regionIntegral_smul σ hf).1
  · intro hf
    simpa only [sign_involution hσ] using (regionIntegral_smul σ hf).1

lemma sign_mul_abs (t : ℝ) : Real.sign t * |t| = t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]; ring
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht, one_mul]

/-- Generic open-domain version allows restricting the homeomorphism to
an individual component without changing ambient derivative representatives. -/
lemma signed_open_on {U V : Set (E n)} (e : U ≃ₜ V) (φ ψ : E n → E n)
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ 1 φ U)
    (hψ : ContDiffOn ℝ 1 ψ V) (he : ∀ x : U, φ x = e x)
    (hei : ∀ y : V, ψ y = e.symm y)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hor : ∀ x ∈ U, Real.sign ((fderiv ℝ φ x).det) = σ)
    (f : V → ℝ) (hb : RegionBounded f) (hk : HasCompactSupport f) :
    let g : U → ℝ := fun x =>
      pullback φ (fun y => zeroExtension f y • volumeForm n) x (standardBasis n)
    RegionBounded g ∧ HasCompactSupport g ∧
      (OpenIntegrable f ↔ OpenIntegrable g) ∧
      ((OpenIntegrable f ∨ OpenIntegrable g) → openIntegral g = σ * openIntegral f) := by
  let p : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
  have hsub := RiemannSubstitution.riemann_substitution e φ ψ hU hV hφ hψ he hei f hb hk
  have hg : (fun x : U =>
      pullback φ (fun y => zeroExtension f y • volumeForm n) x (standardBasis n)) =
      fun x => σ * p x := by
    funext x
    rw [pullback_coefficient, he x, zeroExtension_apply f (e x)]
    have hd : (fderiv ℝ φ x).det = σ * |(fderiv ℝ φ x).det| := by
      rw [← hor x x.property, sign_mul_abs]
    rw [hd]
    dsimp [p]
    ring
  rw [hg]
  have hiff : OpenIntegrable f ↔ OpenIntegrable (fun x => σ * p x) :=
    hsub.2.2.2.2.1.trans (openIntegrable_sign_iff hσ p)
  refine ⟨regionBounded_smul σ hsub.1, hsub.2.1.mul_left, hiff, ?_⟩
  intro hi
  have hf := hi.elim id hiff.mpr
  exact (openIntegral_smul σ (hsub.2.2.2.2.1.mp hf)).2.trans
    (congrArg (fun t => σ * t) (hsub.2.2.2.2.2 (Or.inl hf)).symm)

theorem signed_open_substitution : Specs.D04.C07.Orientation.signed_open_substitutionType := by
  intro n e he hei σ hσ hor f hb hk
  exact signed_open_on e.toHomeomorphSourceTarget e e.symm e.open_source e.open_target
    he hei (fun _ => rfl) (fun _ => rfl) σ hσ hor f hb hk

theorem signed_region_substitution : Specs.D04.C07.Orientation.signed_region_substitutionType := by
  intro n e he hei S hS hK hU σ hσ hor f hb
  let g : S → ℝ := fun x =>
    pullback e (fun y => zeroExtension f y • volumeForm n) x (standardBasis n)
  change RegionBounded g ∧ (RegionIntegrable f ↔ RegionIntegrable g) ∧
    ((RegionIntegrable f ∨ RegionIntegrable g) → regionIntegral g = σ * regionIntegral f)
  let p : S → ℝ := fun x =>
    f ⟨e x, mem_image_of_mem e x.property⟩ * |(fderiv ℝ e x).det|
  have hsub := RegionSubstitution.region_substitution e he hei S hS hK hU f hb
  have hg : g = fun x => σ * p x := by
    funext x
    dsimp only [g]
    rw [pullback_coefficient, zeroExtension_apply f ⟨e x, mem_image_of_mem e x.property⟩]
    have hd : (fderiv ℝ e x).det = σ * |(fderiv ℝ e x).det| := by
      rw [← hor x x.property, sign_mul_abs]
    rw [hd]
    dsimp [p]
    ring
  rw [hg]
  have hiff : RegionIntegrable f ↔ RegionIntegrable (fun x => σ * p x) :=
    hsub.2.1.trans (regionIntegrable_sign_iff hσ p)
  refine ⟨regionBounded_smul σ hsub.1, hiff, ?_⟩
  intro hi
  have hf := hi.elim id hiff.mpr
  exact (regionIntegral_smul σ (hsub.2.1.mp hf)).2.trans
    (congrArg (fun t => σ * t) (hsub.2.2 (Or.inl hf)).symm)

theorem component_region_substitution :
    Specs.D04.C07.Orientation.component_region_substitutionType := by
  intro n e he hei a ha S hS hK hU hC f hb
  have hs := component_sign e he hei a ha
  exact signed_region_substitution e he hei S hS hK hU _ hs.1
    (fun x hx => hs.2.1 x (hC hx)) f hb

theorem positive_density : Specs.D04.C07.Orientation.positive_densityType :=
  RegionSubstitution.volume_substitution

/-- Restriction is performed before substitution: there is no global sign
assigned to a potentially disconnected diffeomorphism domain. -/
theorem component_open_substitution :
    Specs.D04.C07.Orientation.component_open_substitutionType := by
  intro n e he hei a ha
  let C := connectedComponentIn e.source a
  have hC : IsOpen C := e.open_source.connectedComponentIn
  have hCU : C ⊆ e.source := connectedComponentIn_subset e.source a
  let er := e.restrOpen C hC
  have hs : er.source = C := inter_eq_right.mpr hCU
  have ht : er.target = e '' C := by
    rw [← er.image_source_eq_target, hs]
    rfl
  let ec : C ≃ₜ (e '' C) :=
    ((Homeomorph.setCongr hs.symm).trans er.toHomeomorphSourceTarget).trans
      (Homeomorph.setCongr ht)
  have hT : e '' C ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hCU hx)
  have hTo : IsOpen (e '' C) := ht ▸ er.open_target
  have hec : ∀ x : C, e x = ec x := fun _ => rfl
  have heci : ∀ y : e '' C, e.symm y = ec.symm y := fun _ => rfl
  have hsign := component_sign e he hei a ha
  dsimp only
  intro f hb hk
  exact signed_open_on ec e e.symm hC hTo (he.mono hCU) (hei.mono hT)
    hec heci _ hsign.1 hsign.2.1 f hb hk

end D04.Orientation
