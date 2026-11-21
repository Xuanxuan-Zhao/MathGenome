import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.ImmersionsEmbeddingsAndExamples
import MathGenome.Internal.MultivariableAnalysis.D04.C14.RegularLevelsAndGraphs
import MathGenome.Internal.MultivariableAnalysis.D04.C04.SubmersionImmersion
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CompactContinuity
import MathGenome.Internal.MultivariableAnalysis.D04.C09.CircleMultiplicity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04.C14.ImmersionsEmbeddingsAndExamples
open D04
open Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model

abbrev Immersion := @Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model.Immersion
abbrev Embedding := @Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model.Embedding
abbrev realParameter := Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model.realParameter
abbrev circleParam := Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model.circleParam
abbrev turnDomain := Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model.turnDomain
abbrev unitSphere := Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model.unitSphere
abbrev inverseAngle := Specs.D04.C14.ImmersionsEmbeddingsAndExamples.Model.inverseAngle

open Specs.D04.C14.ImmersionsEmbeddingsAndExamples

 theorem immersion_open_iff : immersion_open_iffType := by
  intro r k n V f hV
  exact and_congr_right (fun _ => open_fullRankLocalExtension_iff V f hV)

 theorem embedding_agreement : embedding_agreementType := by
  intro r k n V f
  constructor
  · rintro ⟨hf, he⟩
    exact ⟨hf, embeddingOn_homeomorph f V he⟩
  · rintro ⟨hf, e, he⟩
    refine ⟨hf, ?_⟩
    have hEq : (fun u : V => f u) = (Subtype.val ∘ e) := by
      funext u
      exact (he u).symm
    change Topology.IsEmbedding (fun u : V => f u)
    rw [hEq]
    exact Topology.IsEmbedding.subtypeVal.comp e.isEmbedding

 theorem immersion_continuous {r : ℕ∞ω} {k n : ℕ} {V : Set (E k)}
    {f : E k → E n} (hf : Immersion r V f) : ContinuousOn f V := by
  intro u hu
  obtain ⟨W, g, hW, huW, he, hg, _⟩ := hf.2 u hu
  have heq : f =ᶠ[𝓝[V] u] g := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW)]
      with x hx hxW
    exact (he ⟨hx, hxW⟩).symm
  exact ((hg.continuousOn u huW).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))).congr_of_eventuallyEq heq
    (he ⟨hu, huW⟩).symm

 theorem immersion_mono {r : ℕ∞ω} {k n : ℕ} {V T : Set (E k)}
    {f : E k → E n} (hf : Immersion r V f) (hTV : T ⊆ V) : Immersion r T f := by
  refine ⟨hf.1, ?_⟩
  intro u hu
  obtain ⟨W, g, hW, huW, he, hg, hDg⟩ := hf.2 u (hTV hu)
  exact ⟨W, g, hW, huW, he.mono (inter_subset_inter_left W hTV), hg, hDg⟩

 theorem immersion_local_patch : immersion_local_patchType := by
  intro r k n V f half hhalf hV hf u hu
  obtain ⟨W₀, g₀, _, hu₀, _, _, hD₀⟩ := hf.2 u hu
  have hkn : k ≤ n := by
    have h := LinearMap.finrank_le_finrank_of_injective (hD₀ u hu₀)
    simpa only [finrank_euclideanSpace_fin] using h
  obtain ⟨s, W, g, X, Y, q, h⟩ := local_graph_and_ambient_inverse
    V f u half hf.1 hkn hhalf hV hf.2 hu
  have hX := h.inverse.1
  have huX := h.inverse.2.2.1
  have hreg := immersion_mono hf (inter_subset_left : V ∩ X ⊆ V)
  have hc : ContinuousOn f (V ∩ X) := immersion_continuous hreg
  let J := q ∘ coordinateProjection s
  have hJ : ContinuousOn J (f '' (V ∩ X)) :=
    h.inverse_ambient_regular.continuousOn.mono (by
      rintro _ ⟨v, hv, rfl⟩
      exact (h.projected_domain ▸ mem_image_of_mem (coordinateProjection s ∘ f) hv).1)
  let c : EmbeddedChart r k n (f '' (V ∩ X)) := {
    half := half
    half_pos := hhalf
    source := V ∩ X
    source_open := by
      obtain ⟨O, hO, he⟩ := hV
      exact ⟨O ∩ X, hO.inter hX, by rw [he, inter_assoc]⟩
    ambient := univ
    ambient_open := isOpen_univ
    toFun := f
    invFun := J
    map_source := fun v hv => ⟨mem_image_of_mem f hv, mem_univ _⟩
    map_target := fun _ hx => h.inverse_maps hx.1
    left_inv := h.inverse_left
    right_inv := fun _ hx => h.inverse_right hx.1
    continuous_toFun := hc
    continuous_invFun := hJ.mono inter_subset_left
    regular := hreg.2 }
  refine ⟨X, c, hX, huX, rfl, rfl, rfl, hreg, ?_⟩
  change Topology.IsEmbedding (fun v : ↥(V ∩ X) => f v)
  exact Topology.IsEmbedding.subtypeVal.comp c.homeomorph.isEmbedding

 theorem compact_injective_homeomorph : compact_injective_homeomorphType := by
  intro X _ _ n f hf hi
  exact ⟨(hf.isClosedEmbedding hi).isEmbedding.toHomeomorph, fun _ => rfl⟩

 theorem compact_injective_immersion : compact_injective_immersionType := by
  intro r k n V f hV hf hi
  let : CompactSpace V := isCompact_iff_compactSpace.mp hV
  exact ⟨hf, ((immersion_continuous hf).domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hi x.property y.property h))).isEmbedding⟩


open D04.C09.CircleMultiplicity

/-- The single Euclidean coordinate is an actual continuous linear equivalence. -/
def parameterEquiv : E 1 ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)

@[simp] theorem parameterEquiv_apply (u : E 1) : parameterEquiv u = u 0 := rfl
@[simp] theorem parameterEquiv_symm_apply (t : ℝ) : parameterEquiv.symm t = realParameter t := rfl

 theorem circleParam_smooth (m : ℤ) : ContDiff ℝ ∞ (circleParam m) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · exact (Real.contDiff_cos.comp (contDiff_const.mul parameterEquiv.contDiff))
  · exact (Real.contDiff_sin.comp (contDiff_const.mul parameterEquiv.contDiff))

 theorem circleParam_derivative (m : ℤ) (u : E 1) :
    HasFDerivAt (circleParam m)
      ((ContinuousLinearMap.smulRight parameterEquiv.toContinuousLinearMap
        (circleVelocity m (u 0)))) u := by
  exact (circle_derivative m (u 0)).hasFDerivAt.comp u parameterEquiv.hasFDerivAt

 theorem circleParam_injective_derivative (m : ℤ) (hm : m ≠ 0) (u : E 1) :
    ImmersionAt (circleParam m) u := by
  change Function.Injective (fderiv ℝ (circleParam m) u)
  rw [(circleParam_derivative m u).fderiv]
  have hv : circleVelocity m (u 0) ≠ 0 := by
    intro hz
    have hs := circle_speed m (u 0)
    rw [hz, norm_zero] at hs
    have : (m : ℝ) = 0 := abs_eq_zero.mp hs.symm
    exact hm (by exact_mod_cast this)
  intro v w he
  apply parameterEquiv.injective
  exact (smul_left_injective ℝ hv) he

 theorem circle_immersion : circle_immersionType := by
  intro m hm
  have hr : ManifoldRegularity ∞ := ⟨by simp, le_rfl⟩
  have hI : Immersion ∞ univ (circleParam m) :=
    (immersion_open_iff _ _ isOpen_univ).mpr
      ⟨hr, (circleParam_smooth m).contDiffOn, fun u _ => circleParam_injective_derivative m hm u⟩
  exact ⟨hI, fun u => ⟨circleParam_injective_derivative m hm u,
    SubmersionImmersion.rank_of_immersion _ _ (circleParam_injective_derivative m hm u)⟩⟩

 theorem circle_one_injOn : InjOn (circle 1) (Ico (0 : ℝ) (2*Real.pi)) := by
  intro s hs t ht he
  have hc : Real.cos s = Real.cos t := by
    simpa using congrArg (fun x : E 2 => x 0) he
  have hsin : Real.sin s = Real.sin t := by
    simpa using congrArg (fun x : E 2 => x 1) he
  let : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2*Real.pi) (a := (0 : ℝ))
    (by simpa using hs) (by simpa using ht)).mp (Real.Angle.cos_sin_inj hc hsin)

 theorem circle_one_surjOn : SurjOn (circle 1) (Ico (0 : ℝ) (2*Real.pi)) (unitSphere 2) := by
  intro x hx
  obtain ⟨t, ht, hc, hs⟩ := unit_circle_angle x hx
  have hxt : circle 1 t = x := by
    ext i
    fin_cases i <;> simp [hc, hs]
  by_cases hlt : t < 2*Real.pi
  · exact ⟨t, ⟨ht.1, hlt⟩, hxt⟩
  · have he : t = 2*Real.pi := le_antisymm ht.2 (le_of_not_gt hlt)
    refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
    rw [he, ← circle_closed] at hxt
    exact hxt

 theorem circle_twice_scale (t : ℝ) : circle 2 t = circle 1 (2*t) := by
  ext i
  fin_cases i <;> simp

 theorem circle_twice_shift (t : ℝ) : circle 2 (t+Real.pi) = circle 2 t := by
  ext i
  fin_cases i
  · change Real.cos ((2 : ℤ)* (t+Real.pi)) = Real.cos ((2 : ℤ)*t)
    push_cast
    rw [mul_add, Real.cos_add_two_pi]
  · change Real.sin ((2 : ℤ)* (t+Real.pi)) = Real.sin ((2 : ℤ)*t)
    push_cast
    rw [mul_add, Real.sin_add_two_pi]

 theorem twice_traversed_circle : twice_traversed_circleType := by
  have hfirst : BijOn (circle 2) (Ico (0 : ℝ) Real.pi) (unitSphere 2) := by
    refine ⟨fun t _ => circle_norm 2 t, ?_, ?_⟩
    · intro s hs t ht he
      have he' := circle_one_injOn (x₁ := 2*s) (x₂ := 2*t)
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
        ((circle_twice_scale s).symm.trans (he.trans (circle_twice_scale t)))
      linarith
    · intro x hx
      obtain ⟨t, ht, he⟩ := circle_one_surjOn hx
      refine ⟨t/2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      rw [circle_twice_scale, show 2*(t/2) = t by ring, he]
  refine ⟨hfirst, ?_, ?_, ?_⟩
  · refine ⟨fun t _ => circle_norm 2 t, ?_, ?_⟩
    · intro s hs t ht he
      have hs' : s-Real.pi ∈ Ico (0 : ℝ) Real.pi := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have ht' : t-Real.pi ∈ Ico (0 : ℝ) Real.pi := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hp (v : ℝ) : circle 2 (v-Real.pi) = circle 2 v := by
        have hh := circle_twice_shift (v-Real.pi)
        simpa using hh.symm
      have := hfirst.injOn hs' ht' ((hp s).trans (he.trans (hp t).symm))
      linarith
    · intro x hx
      obtain ⟨t, ht, he⟩ := hfirst.surjOn hx
      exact ⟨t+Real.pi, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        (circle_twice_shift t).trans he⟩
  · intro hi
    have hh := hi (x₁ := 0) (x₂ := Real.pi) ⟨le_rfl, by positivity⟩
      ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
      (by simpa using (circle_twice_shift 0).symm)
    exact Real.pi_ne_zero hh.symm
  · change D04.C09.length (circle 2) 0 (2*Real.pi) = _
    rw [circle_length]
    congr 1
    norm_num
    ring


 theorem twice_circle_fibers : twice_circle_fibersType := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := twice_traversed_circle.1.surjOn hx
  obtain ⟨t, ht, htx⟩ := twice_traversed_circle.2.1.surjOn hx
  refine ⟨s, hs, t, ht, (by intro he; linarith [hs.2, ht.1]), hsx, htx, ?_⟩
  intro v hv
  constructor
  · intro hvx
    by_cases hlt : v < Real.pi
    · exact Or.inl (twice_traversed_circle.1.injOn ⟨hv.1, hlt⟩ hs (hvx.trans hsx.symm))
    · exact Or.inr (twice_traversed_circle.2.1.injOn ⟨le_of_not_gt hlt, hv.2⟩ ht
        (hvx.trans htx.symm))
  · rintro (rfl | rfl) <;> assumption

 theorem sphere_boundaries : sphere_boundariesType := by
  intro n r hr
  let g : E (n+1) → E 1 := fun x => realParameter (‖x‖^2 - 1)
  have hg : ContDiff ℝ r g := parameterEquiv.symm.contDiff.comp
    ((contDiff_norm_sq ℝ).sub contDiff_const)
  have hzero : univ ∩ g ⁻¹' {0} = unitSphere (n+1) := by
    ext x
    simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_singleton_iff]
    constructor
    · intro hx
      have hs : ‖x‖^2 - 1 = 0 := congrArg (fun y : E 1 => y 0) hx
      change ‖x‖ = 1
      nlinarith [norm_nonneg x]
    · intro hx
      have hx' : ‖x‖ = 1 := hx
      change realParameter (‖x‖^2 - 1) = 0
      rw [hx']
      ext i
      norm_num [realParameter, Model.realParameter]
  have hsurj : ∀ x ∈ univ, g x = 0 → Function.Surjective (fderiv ℝ g x) := by
    intro x _ hx
    have hnorm : ‖x‖ = 1 := by
      have : x ∈ univ ∩ g ⁻¹' {0} := ⟨mem_univ _, hx⟩
      rw [hzero] at this
      exact this
    have hd := parameterEquiv.symm.hasFDerivAt.comp x
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1)
    have hdg : HasFDerivAt g
      (parameterEquiv.symm.toContinuousLinearMap.comp (2 • innerSL ℝ x)) x := hd
    intro y
    refine ⟨((y 0)/2) • x, ?_⟩
    rw [hdg.fderiv]
    apply parameterEquiv.injective
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, smul_apply,
      innerSL_apply_apply, parameterEquiv_apply]
    simp only [two_smul, inner_smul_right, real_inner_self_eq_norm_sq, hnorm]
    ring
  have hdim : n+1-n = 1 := by omega
  have hlevel := (RegularLevels.regular_zero_set (r := r) (k := n) (n := n+1))
  rw [hdim] at hlevel
  have hM := hlevel univ g hr (by omega) isOpen_univ hg.contDiffOn
    (fun x hx hz => RegularLevels.range_finrank_of_surjective _ (hsurj x hx hz))
  rw [hzero] at hM
  refine ⟨(boundaryless_iff.mp hM).1, (boundaryless_iff.mp hM).2, ?_⟩
  have he : unitSphere (n+1) = Metric.sphere (0 : E (n+1)) 1 := by
    ext x
    simp [unitSphere, Model.unitSphere]
  change frontier (unitSphere (n+1)) = unitSphere (n+1)
  rw [he]
  exact frontier_sphere _ one_ne_zero


 theorem inverseAngle_left (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (2*Real.pi)) :
    inverseAngle (circle 1 t) = t := by
  classical
  unfold inverseAngle Model.inverseAngle
  split_ifs with h
  · exact circle_one_injOn (Classical.choose_spec h).1 ht (Classical.choose_spec h).2
  · exact False.elim (h ⟨t, ht, rfl⟩)

 theorem inverseAngle_discontinuous :
    ¬ ContinuousWithinAt inverseAngle (unitSphere 2) (circle 1 0) := by
  intro hc
  let t : ℕ → ℝ := fun j => 2*Real.pi*(1-1/((j:ℝ)+1))
  have ht : ∀ j, t j ∈ Ico (0 : ℝ) (2*Real.pi) := by
    intro j
    have hd : 0 < (j:ℝ)+1 := by positivity
    have hrec : 1 / ((j:ℝ)+1) ≤ 1 := (div_le_one₀ hd).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hpos : 0 < 1 / ((j:ℝ)+1) := by positivity
    constructor <;> dsimp [t] <;> nlinarith [Real.pi_pos]
  have htlim : Tendsto t atTop (𝓝 (2*Real.pi)) := by
    have hh := (tendsto_const_nhds (x := (2*Real.pi))).mul
      ((tendsto_const_nhds (x := (1:ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa [t] using hh
  have hcircle : Continuous (circle 1) := continuous_iff_continuousAt.mpr
    (fun s => (circle_derivative 1 s).continuousAt)
  have hlim : Tendsto (fun j => circle 1 (t j)) atTop (𝓝 (circle 1 0)) := by
    have hh := hcircle.continuousAt.tendsto.comp htlim
    rwa [← circle_closed] at hh
  have hlimWithin : Tendsto (fun j => circle 1 (t j)) atTop
      (𝓝[unitSphere 2] (circle 1 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun j => circle_norm 1 (t j))⟩
  have hzero : inverseAngle (circle 1 0) = 0 := inverseAngle_left 0 ⟨le_rfl, by positivity⟩
  have hcontr : Tendsto t atTop (𝓝 (0:ℝ)) := by
    have hh := hc.tendsto.comp hlimWithin
    rw [hzero] at hh
    exact hh.congr (fun j => inverseAngle_left (t j) (ht j))
  have he := tendsto_nhds_unique htlim hcontr
  nlinarith [Real.pi_pos]

 theorem half_open_circle : half_open_circleType := by
  have hi : InjOn (circleParam 1) turnDomain := by
    intro u hu v hv huv
    apply parameterEquiv.injective
    exact circle_one_injOn hu hv huv
  have heq : circleParam 1 '' turnDomain = unitSphere 2 := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact circle_norm 1 (u 0)
    · intro hx
      obtain ⟨t, ht, he⟩ := circle_one_surjOn hx
      exact ⟨realParameter t, ht, he⟩
  have hf : Immersion ∞ turnDomain (circleParam 1) :=
    immersion_mono ((circle_immersion 1 (by norm_num)).1) (subset_univ _)
  have hne : ¬ Embedding ∞ turnDomain (circleParam 1) := by
    intro hE
    obtain ⟨_, e, he⟩ := (embedding_agreement turnDomain (circleParam 1)).mp hE
    have hc : Continuous (fun x : (circleParam 1 '' turnDomain) =>
        parameterEquiv (e.symm x)) := parameterEquiv.continuous.comp
      (continuous_subtype_val.comp e.symm.continuous)
    have hcinv : ContinuousOn inverseAngle (circleParam 1 '' turnDomain) := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      apply hc.congr
      intro x
      have hfx : circleParam 1 (e.symm x) = x := by
        rw [← he (e.symm x)]
        simp
      have hh := inverseAngle_left ((e.symm x).val 0) (e.symm x).property
      change inverseAngle (circleParam 1 (e.symm x)) = _ at hh
      rw [hfx] at hh
      exact hh.symm
    rw [heq] at hcinv
    exact inverseAngle_discontinuous (hcinv _ (circle_norm 1 0))
  refine ⟨hi, heq, hf, inverseAngle_left, inverseAngle_discontinuous, hne, ?_⟩
  intro hcompact
  exact hne (compact_injective_immersion _ _ hcompact hf hi)

end D04.C14.ImmersionsEmbeddingsAndExamples
