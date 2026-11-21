import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.StrictDualSmoothness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.LocalLipschitzSubgradients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Mathlib.Analysis.Convex.Mul

/-! Strict convexity of the real continuous dual gives a singleton duality
map and the Gâteaux derivative of half the squared norm. Fixed supporting
secants prove norm-to-weak-star continuity, including convergence along
arbitrary filters. Reflexivity and strict convexity of the primal space give
the canonical inverse formula. These are the strictness conclusions of
`fa2:p2:duality-smoothness`; uniform smoothness is a separate obligation. -/
namespace ExpandedFA.BanachConvex
open Filter Set
open scoped Topology
universe u v
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma dualityMap_nonempty (x : X) : (dualityMap X x).Nonempty := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp [dualityMap]⟩
  · obtain ⟨f, hf, hfx⟩ := P1.C05Norming.norming_functional_nonzero ℝ X x hx
    refine ⟨‖x‖ • f, ?_, ?_⟩
    · simp [norm_smul, hf]
    · simp [hfx, pow_two]

lemma dualityMap_subsingleton [StrictConvexSpace ℝ (X →L[ℝ] ℝ)] (x : X) :
    (dualityMap X x).Subsingleton := by
  intro f hf g hg
  by_cases hx : x = 0
  · have hf0 : f = 0 := norm_eq_zero.mp (hf.1.trans (by simp [hx]))
    have hg0 : g = 0 := norm_eq_zero.mp (hg.1.trans (by simp [hx]))
    exact hf0.trans hg0.symm
  · by_contra hne
    have hlt := norm_combo_lt_of_ne hf.1.le hg.1.le hne
      (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    have hb := ((1/2 : ℝ) • f + (1/2 : ℝ) • g).le_opNorm x
    have hv : ((1/2 : ℝ) • f + (1/2 : ℝ) • g) x = ‖x‖ ^ 2 := by
      simp only [add_apply, smul_apply, smul_eq_mul, hf.2, hg.2]
      ring
    rw [Real.norm_eq_abs, hv, abs_of_nonneg (sq_nonneg _)] at hb
    have hn := norm_pos_iff.mpr hx
    nlinarith

theorem dualityMap_singleton : StrictDualSpec.SingleValued.{u} := by
  classical
  intro X _ _ _ _
  choose J hJ using (dualityMap_nonempty (X := X))
  refine ⟨J, fun x => ?_⟩
  change dualityMap X x = {J x}
  exact Set.Subset.antisymm (fun _ hf => (dualityMap_subsingleton x hf (hJ x)))
    (by simpa only [singleton_subset_iff] using hJ x)

lemma selection_mem (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x}) (x : X) :
    J x ∈ dualityMap X x := by
  change J x ∈ Spec.DualityMapValue X x
  rw [hJ x]
  exact mem_singleton _

theorem duality_pairing_identity : StrictDualSpec.PairingIdentity.{u} := by
  intro X _ _ _ _ J hJ x y
  have hx := (selection_mem J hJ x).2
  have hy := (selection_mem J hJ y).2
  simp only [add_apply, sub_apply, map_add, map_sub]
  linarith

/-- Symmetry of the defining norm and pairing equations under canonical evaluation. -/
lemma dualityMap_canonical_iff (x : X) (f : X →L[ℝ] ℝ) :
    P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X x ∈
      dualityMap (X →L[ℝ] ℝ) f ↔ f ∈ dualityMap X x := by
  change (‖P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X x‖ = ‖f‖ ∧
    f x = ‖f‖ ^ 2) ↔ (‖f‖ = ‖x‖ ∧ f x = ‖x‖ ^ 2)
  rw [P1.C05BidualIsometry.canonicalEvaluation_norm ℝ X x]
  constructor <;> rintro ⟨h, he⟩
  · exact ⟨h.symm, by simpa only [h] using he⟩
  · exact ⟨h.symm, by simpa only [h] using he⟩

lemma dualityMap_primal_unique [StrictConvexSpace ℝ X]
    (f : X →L[ℝ] ℝ) {x y : X}
    (hx : f ∈ dualityMap X x) (hy : f ∈ dualityMap X y) : x = y := by
  by_cases hf : f = 0
  · have hx0 : x = 0 := norm_eq_zero.mp (hx.1.symm.trans (by simp [hf]))
    have hy0 : y = 0 := norm_eq_zero.mp (hy.1.symm.trans (by simp [hf]))
    exact hx0.trans hy0.symm
  · by_contra hne
    have hlt := norm_combo_lt_of_ne hx.1.symm.le hy.1.symm.le hne
      (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    have hb := f.le_opNorm ((1/2 : ℝ) • x + (1/2 : ℝ) • y)
    have hv : f ((1/2 : ℝ) • x + (1/2 : ℝ) • y) = ‖f‖ ^ 2 := by
      simp only [map_add, map_smul, smul_eq_mul, hx.2, hy.2, ← hx.1, ← hy.1]
      ring
    rw [Real.norm_eq_abs, hv, abs_of_nonneg (sq_nonneg _)] at hb
    have hn := norm_pos_iff.mpr hf
    nlinarith

theorem duality_bijective_inverse : StrictDualSpec.BijectiveInverse.{u} := by
  classical
  intro X _ _ _ _ _ href J hJ
  have hinj : Function.Injective J := by
    intro x y hxy
    apply dualityMap_primal_unique (J x) (selection_mem J hJ x)
    rw [hxy]
    exact selection_mem J hJ y
  have hsurj : Function.Surjective J := by
    intro f
    obtain ⟨F, hF⟩ := dualityMap_nonempty (X := X →L[ℝ] ℝ) f
    obtain ⟨x, hx⟩ := href F
    have hfx : f ∈ Spec.DualityMapValue X x :=
      (dualityMap_canonical_iff x f).mp (by rwa [hx])
    rw [hJ x] at hfx
    exact ⟨x, (mem_singleton_iff.mp hfx).symm⟩
  let e : X ≃ (X →L[ℝ] ℝ) := Equiv.ofBijective J ⟨hinj, hsurj⟩
  refine ⟨⟨hinj, hsurj⟩, e.symm, e.symm_apply_apply, e.apply_symm_apply, ?_⟩
  intro f
  apply Set.Subset.antisymm
  · intro F hF
    obtain ⟨x, rfl⟩ := href F
    have hx : f ∈ Spec.DualityMapValue X x := (dualityMap_canonical_iff x f).mp hF
    rw [hJ x] at hx
    have he : e x = f := (mem_singleton_iff.mp hx).symm
    have hx' : x = e.symm f := by rw [← he, e.symm_apply_apply]
    exact mem_singleton_iff.mpr (congrArg _ hx')
  · rw [singleton_subset_iff]
    apply (dualityMap_canonical_iff (e.symm f) f).mpr
    have hm := selection_mem J hJ (e.symm f)
    have he : J (e.symm f) = f := e.apply_symm_apply f
    rwa [he] at hm

/-- The finite convex quadratic used throughout this theorem. -/
lemma halfNormSquare_convex :
    P1.ExtendedConvexFunctions.ExtendedConvex X
      (Asplund.NormSquareConjugate.halfNormSquare norm) := by
  have hc : ConvexOn ℝ (univ : Set X) (fun x : X => ‖x‖ ^ 2 / 2) := by
    have hh := ((convexOn_norm (convex_univ : Convex ℝ (univ : Set X))).pow
      (fun x _ => norm_nonneg x) 2).smul (c := (1/2 : ℝ)) (by norm_num)
    simpa only [smul_eq_mul, Pi.pow_apply, div_eq_mul_inv, one_mul, mul_comm] using hh
  intro x y r s a b hx hy ha hb hab
  have hx' : ‖x‖ ^ 2 / 2 = r := WithTop.coe_inj.mp hx
  have hy' : ‖y‖ ^ 2 / 2 = s := WithTop.coe_inj.mp hy
  change ((‖a • x + b • y‖ ^ 2 / 2 : ℝ) : WithTop ℝ) ≤ _
  rw [WithTop.coe_le_coe]
  simpa only [smul_eq_mul, hx', hy'] using hc.2 (mem_univ x) (mem_univ y) ha hb hab

/-- The attaining directional maximum becomes a linear functional when the
subdifferential is a singleton. -/
lemma halfNormSquare_right_derivative (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x}) (x v : X) :
    Tendsto (fun t : ℝ => (‖x + t • v‖ ^ 2 / 2 - ‖x‖ ^ 2 / 2) / t)
      (𝓝[>] 0) (𝓝 (J x v)) := by
  let φ := Asplund.NormSquareConjugate.halfNormSquare (norm : X → ℝ)
  have hproper : P1.ExtendedConvexFunctions.Proper X φ :=
    ⟨0, WithTop.coe_ne_top⟩
  have hb : ∀ y ∈ Metric.closedBall x 1,
      φ y ≤ (((‖x‖ + 1) ^ 2 / 2 : ℝ) : WithTop ℝ) := by
    intro y hy
    have hn : ‖y‖ ≤ ‖x‖ + 1 := by
      have hh := norm_sub_le y x
      have ht := norm_add_le (y - x) x
      rw [sub_add_cancel] at ht
      have hd : ‖y - x‖ ≤ 1 := mem_closedBall_iff_norm.mp hy
      linarith
    change ((‖y‖ ^ 2 / 2 : ℝ) : WithTop ℝ) ≤ _
    rw [WithTop.coe_le_coe]
    nlinarith [norm_nonneg y, norm_nonneg x]
  obtain ⟨d, hd, ⟨f, hf, hfv⟩, _⟩ :=
    directional_derivative_maximum X φ x 1 ((‖x‖ + 1) ^ 2 / 2)
      hproper halfNormSquare_convex zero_lt_one hb v
  have he : f = J x := by
    have hm : f ∈ Spec.DualityMapValue X x := by
      rw [← halfNormSquare_subdifferential X x]
      exact hf
    rwa [hJ x, mem_singleton_iff] at hm
  rw [he] at hfv
  simpa only [LocalSpec.realValue, φ, Asplund.NormSquareConjugate.halfNormSquare,
    WithTop.untopD_coe, ← hfv] using hd

theorem halfNormSquare_gateaux : StrictDualSpec.GateauxDifferentiability.{u} := by
  intro X _ _ _ _ J hJ x v
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  constructor
  · have hh := (halfNormSquare_right_derivative J hJ x (-v)).neg.comp
      (show Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝[>] 0) by
        simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ))))
    simpa [slope_fun_def_field, Function.comp_def, map_neg, smul_neg, neg_smul, neg_div, div_neg] using hh
  · simpa [slope_fun_def_field] using halfNormSquare_right_derivative J hJ x v

lemma halfNormSquare_support (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x}) (y z : X) :
    ‖y‖ ^ 2 / 2 + J y (z - y) ≤ ‖z‖ ^ 2 / 2 := by
  have hf := selection_mem J hJ y
  change J y ∈ Spec.DualityMapValue X y at hf
  rw [← halfNormSquare_subdifferential X y] at hf
  exact (mem_subdifferential_iff_of_value _ y (‖y‖ ^ 2 / 2) rfl (J y)).mp hf
    z (‖z‖ ^ 2 / 2) rfl

/-- Fixed positive secants bound every nearby supporting functional.
This avoids any sequential compactness assumption. -/
lemma eventually_duality_eval_lt (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x})
    (x v : X) (b : ℝ) (hb : J x v < b) :
    ∀ᶠ y in 𝓝 x, J y v < b := by
  have he := (halfNormSquare_right_derivative J hJ x v).eventually
    (eventually_lt_nhds hb)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, htb⟩ := (hpos.and he).exists
  have hcont : Continuous (fun y : X =>
      (‖y + t • v‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2) / t) := by
    fun_prop
  have hnear := (hcont.continuousAt (x := x)).eventually (eventually_lt_nhds htb)
  filter_upwards [hnear] with y hy
  have hs := halfNormSquare_support J hJ y (y + t • v)
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at hs
  have hbound : J y v ≤ (‖y + t • v‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2) / t := by
    apply (le_div_iff₀ ht).mpr
    linarith
  exact hbound.trans_lt hy

lemma duality_eval_continuous (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x}) (v : X) :
    Continuous (fun x => J x v) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hneg : J x (-v) < -a := by simpa only [map_neg] using neg_lt_neg ha
    filter_upwards [eventually_duality_eval_lt J hJ x (-v) (-a) hneg] with y hy
    simp only [map_neg] at hy
    linarith
  · intro b hb
    exact eventually_duality_eval_lt J hJ x v b hb

theorem duality_weakStar_continuous : StrictDualSpec.WeakStarContinuity.{u} := by
  intro X _ _ _ _ J hJ
  rw [P1.C12WeakStar.weakStarTopology_native ℝ X]
  apply continuous_induced_rng.mpr
  apply WeakDual.continuous_of_continuous_eval
  intro v
  exact duality_eval_continuous J hJ v

theorem duality_net_continuous : StrictDualSpec.NetContinuity.{u, v} := by
  intro X _ _ _ _ J hJ A l z x hz
  have hcont := duality_weakStar_continuous X J hJ
  have ht := @Continuous.tendsto X (X →L[ℝ] ℝ) inferInstance
    (P1.C12WeakStar.Spec.WeakStarTopologyValue ℝ X) J hcont x
  exact ht.comp hz

end ExpandedFA.BanachConvex
