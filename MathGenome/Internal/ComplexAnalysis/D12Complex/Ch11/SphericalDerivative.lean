import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalDerivative
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.ChordalMetric
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.ScalarSphereBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open scoped Topology
open Filter Set
namespace D12Complex.SphericalDerivative
open D12Complex.Chordal

namespace Definitions
abbrev scalarDensity := D12Complex.SphericalDerivative.scalarDensity
abbrev sphericalDeriv := D12Complex.SphericalDerivative.sphericalDeriv
end Definitions

theorem scalarDensity_congr {f g : ℂ → ℂ} {a : ℂ} (he : f =ᶠ[𝓝 a] g) :
    scalarDensity f a = scalarDensity g a := by
  unfold scalarDensity
  rw [he.deriv_eq, he.self_of_nhds]

theorem scalarDensity_inv (f : ℂ → ℂ) (a : ℂ)
    (hf : DifferentiableAt ℂ f a) (ha : f a ≠ 0) :
    scalarDensity (fun z => (f z)⁻¹) a = scalarDensity f a := by
  unfold scalarDensity
  rw [(hf.hasDerivAt.fun_inv ha).deriv]
  simp only [norm_neg, norm_div, norm_pow, norm_inv]
  have hn : ‖f a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  field_simp
  ring

theorem sphericalDeriv_finite (F : ℂ → RiemannSphere) (a : ℂ)
    (ha : F a ≠ sphereInfty) :
    sphericalDeriv F a = scalarDensity (fun z => finiteCoordinate (F z)) a := by
  simp [sphericalDeriv, ha]

theorem sphericalDeriv_congr {F G : ℂ → RiemannSphere} {a : ℂ}
    (he : F =ᶠ[𝓝 a] G) : sphericalDeriv F a = sphericalDeriv G a := by
  unfold sphericalDeriv
  rw [he.self_of_nhds]
  split <;> apply scalarDensity_congr <;> exact he.mono (fun _ h => congrArg _ h)

theorem sphericalDeriv_reciprocal_chart (F : ℂ → RiemannSphere) (a : ℂ)
    (hf : PlaneSphereHolomorphicAt F a) (ha : F a ≠ sphereFinite 0) :
    sphericalDeriv F a = scalarDensity (fun z => infinityCoordinate (F z)) a := by
  by_cases hi : F a = sphereInfty
  · simp [sphericalDeriv, hi]
  · rw [sphericalDeriv_finite _ _ hi]
    have hg := ((planeSphereHolomorphicAt_iff_chart F a .finite hi).mp hf).2
    have he : (fun z => infinityCoordinate (F z)) =
        (fun z => (finiteCoordinate (F z))⁻¹) := by
      funext z
      induction F z using OnePoint.rec <;> simp [infinityCoordinate, finiteCoordinate]
    rw [he]
    symm
    apply scalarDensity_inv (fun z => finiteCoordinate (F z)) a hg.differentiableAt
    intro hzero
    exact ha ((sphere_eq_finiteCoordinate_of_ne_infty hi).trans (congrArg sphereFinite hzero))

theorem sphericalDeriv_scalar (f : ℂ → ℂ) (a : ℂ) :
    sphericalDeriv (sphereFinite ∘ f) a = scalarDensity f a := by
  rw [sphericalDeriv_finite (sphereFinite ∘ f) a (OnePoint.coe_ne_infty (f a))]
  rfl

theorem sphericalDeriv_pole (F : ℂ → RiemannSphere) (a : ℂ)
    (ha : F a = sphereInfty) :
    sphericalDeriv F a = ‖deriv (fun z => infinityCoordinate (F z)) a‖ := by
  simp [sphericalDeriv, ha, scalarDensity, infinityCoordinate_sphereInfty]

theorem sphericalDeriv_in_chart (F : ℂ → RiemannSphere) (a : ℂ) (d : SphereCoordinate)
    (hf : PlaneSphereHolomorphicAt F a) (hd : F a ∈ (sphereCoordinate d).source) :
    sphericalDeriv F a = scalarDensity (fun z => sphereCoordinate d (F z)) a := by
  cases d
  · exact sphericalDeriv_finite F a hd
  · exact sphericalDeriv_reciprocal_chart F a hf hd

theorem sphericalDeriv_nonneg (F : ℂ → RiemannSphere) (a : ℂ) :
    0 ≤ sphericalDeriv F a := by
  unfold sphericalDeriv scalarDensity
  split <;> positivity

theorem sphericalDeriv_const (p : RiemannSphere) (a : ℂ) :
    sphericalDeriv (fun _ => p) a = 0 := by
  unfold sphericalDeriv scalarDensity
  split <;> simp

theorem scalarDensity_continuousAt {f : ℂ → ℂ} {a : ℂ}
    (hf : HolomorphicGermAt f a) : ContinuousAt (scalarDensity f) a := by
  have h : AnalyticAt ℂ f a := Complex.analyticAt_iff_eventually_differentiableAt.mpr
    ((holomorphicGermAt_iff_eventually f a).mp hf)
  exact h.deriv.continuousAt.norm.div
    (continuousAt_const.add (hf.differentiableAt.continuousAt.norm.pow 2)) (by positivity)

theorem sphericalDeriv_continuousOn (Ω : Set ℂ) (F : ℂ → RiemannSphere)
    (hf : PlaneSphereHolomorphicOn Ω F) : ContinuousOn (sphericalDeriv F) Ω := by
  intro a ha
  have hF := hf.2 a ha
  by_cases hi : F a = sphereInfty
  · have hn : F a ≠ sphereFinite 0 := by rw [hi]; exact OnePoint.infty_ne_coe 0
    have hg := ((planeSphereHolomorphicAt_iff_chart F a .reciprocal hn).mp hF).2
    apply ContinuousAt.continuousWithinAt
    apply (scalarDensity_continuousAt hg).congr_of_eventuallyEq
    filter_upwards [hf.1.mem_nhds ha, hF.1.eventually_ne hn] with z hz hne
    exact (sphericalDeriv_reciprocal_chart F z (hf.2 z hz) hne)
  · apply ContinuousAt.continuousWithinAt
    have hg := ((planeSphereHolomorphicAt_iff_chart F a .finite hi).mp hF).2
    apply (scalarDensity_continuousAt hg).congr_of_eventuallyEq
    filter_upwards [hF.1.eventually_ne hi] with z hz
    exact (sphericalDeriv_finite F z hz)

theorem scalarMeromorphic_sphericalDeriv_continuousOn (Ω : Set ℂ)
    (F : ℂ → RiemannSphere) (hf : ScalarMeromorphicOn Ω F) :
    ContinuousOn (sphericalDeriv F) Ω := by
  apply sphericalDeriv_continuousOn Ω F
  exact scalarMeromorphic_planeSphereHolomorphic hf

/-- A coordinate-free homogeneous formula, at any nonzero local pair. -/
theorem scalarDensity_div (u v : ℂ → ℂ) (a : ℂ)
    (hu : DifferentiableAt ℂ u a) (hv : DifferentiableAt ℂ v a) (ha : v a ≠ 0) :
    scalarDensity (fun z => u z / v z) a =
      ‖deriv u a * v a - u a * deriv v a‖ /
        (Complex.normSq (u a) + Complex.normSq (v a)) := by
  unfold scalarDensity
  rw [(hu.hasDerivAt.fun_div hv.hasDerivAt ha).deriv]
  simp only [norm_div, norm_pow, Complex.normSq_eq_norm_sq]
  have hn : ‖v a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  field_simp
  ring

theorem sphericalDeriv_pair (u v : ℂ → ℂ) (a : ℂ)
    (hu : DifferentiableAt ℂ u a) (hv : DifferentiableAt ℂ v a)
    (ha : u a ≠ 0 ∨ v a ≠ 0) :
    sphericalDeriv (fun z => Mobius.spherePair (u z) (v z)) a =
      ‖deriv u a * v a - u a * deriv v a‖ /
        (Complex.normSq (u a) + Complex.normSq (v a)) := by
  by_cases hva : v a = 0
  · have hua : u a ≠ 0 := ha.resolve_right (not_ne_iff.mpr hva)
    rw [sphericalDeriv, ite_eq_left ((Mobius.spherePair_eq_infty_iff _ _).mpr hva)]
    have he : (fun z => infinityCoordinate (Mobius.spherePair (u z) (v z)))
        =ᶠ[𝓝 a] (fun z => v z / u z) := by
      filter_upwards [hu.continuousAt.eventually_ne hua] with z hz
      rw [Mobius.spherePair_eq_infinityParametrization _ _ hz]
      exact infinityChart.right_inv (mem_univ _)
    rw [scalarDensity_congr he, scalarDensity_div v u a hv hu hua]
    rw [show deriv v a * u a - v a * deriv u a =
      -(deriv u a * v a - u a * deriv v a) by ring, norm_neg, add_comm]
  · rw [sphericalDeriv_finite (fun z => Mobius.spherePair (u z) (v z)) a (fun h => hva ((Mobius.spherePair_eq_infty_iff _ _).mp h))]
    have he : (fun z => finiteCoordinate (Mobius.spherePair (u z) (v z)))
        =ᶠ[𝓝 a] (fun z => u z / v z) := by
      filter_upwards [hv.continuousAt.eventually_ne hva] with z hz
      simp [Mobius.spherePair, hz]
    rw [scalarDensity_congr he, scalarDensity_div u v a hu hv hva]

/-- The canonical charts provide local nonvanishing homogeneous coordinates. -/
theorem local_pair (F : ℂ → RiemannSphere) (a : ℂ)
    (hf : PlaneSphereHolomorphicAt F a) :
    ∃ u v : ℂ → ℂ, HolomorphicGermAt u a ∧ HolomorphicGermAt v a ∧
      (u a ≠ 0 ∨ v a ≠ 0) ∧ F =ᶠ[𝓝 a] (fun z => Mobius.spherePair (u z) (v z)) := by
  have hc : HolomorphicGermAt (fun _ : ℂ => (1 : ℂ)) a :=
    ⟨univ, mem_univ _, isOpen_univ, fun _ _ => differentiableAt_const _⟩
  obtain ⟨hcont, c, ha, hg⟩ := hf
  cases c
  · refine ⟨(fun z => finiteCoordinate (F z)), (fun _ => 1), hg, hc,
      Or.inr one_ne_zero, ?_⟩
    filter_upwards [hcont (isClosed_singleton.isOpen_compl.mem_nhds ha)] with z hz
    rw [Mobius.spherePair_self]
    exact sphere_eq_finiteCoordinate_of_ne_infty hz
  · refine ⟨(fun _ => 1), (fun z => infinityCoordinate (F z)), hc, hg,
      Or.inl one_ne_zero, ?_⟩
    have he := hcont (isClosed_singleton.isOpen_compl.mem_nhds ha)
    filter_upwards [he] with z hz
    rw [Mobius.spherePair_eq_infinityParametrization _ _ one_ne_zero, div_one]
    exact (infinityChart.left_inv hz).symm

theorem sphericalDeriv_chartRotation (F : ℂ → RiemannSphere) (c a : ℂ)
    (hf : PlaneSphereHolomorphicAt F a) :
    sphericalDeriv (chartRotation c ∘ F) a = sphericalDeriv F a := by
  obtain ⟨u, v, hu, hv, ha, he⟩ := local_pair F a hf
  have hud := hu.differentiableAt
  have hvd := hv.differentiableAt
  have hn : ∀ᶠ z in 𝓝 a, u z ≠ 0 ∨ v z ≠ 0 := by
    rcases ha with ha | ha
    · exact (hud.continuousAt.eventually_ne ha).mono (fun _ h => Or.inl h)
    · exact (hvd.continuousAt.eventually_ne ha).mono (fun _ h => Or.inr h)
  have he' : (chartRotation c ∘ F) =ᶠ[𝓝 a]
      (fun z => Mobius.spherePair (u z - c * v z) (star c * u z + v z)) := by
    filter_upwards [he, hn] with z hz hnz
    rw [Function.comp_apply, hz, chartRotation_pair c _ _ hnz]
  rw [sphericalDeriv_congr he', sphericalDeriv_congr he]
  rw [sphericalDeriv_pair (fun z => u z - c * v z) (fun z => star c * u z + v z) a
    (hud.fun_sub (hvd.const_mul c)) ((hud.const_mul (star c)).fun_add hvd) (rotation_pair_nonzero c _ _ ha),
    sphericalDeriv_pair u v a hud hvd ha]
  rw [(hud.hasDerivAt.fun_sub (hvd.hasDerivAt.const_mul c)).deriv,
    ((hud.hasDerivAt.const_mul (star c)).fun_add hvd.hasDerivAt).deriv]
  have heq : (deriv u a - c * deriv v a) * (star c * u a + v a) -
      (u a - c * v a) * (star c * deriv u a + deriv v a) =
      (1 + c * star c) * (deriv u a * v a - u a * deriv v a) := by ring
  rw [heq, norm_mul, rotation_pair_weight]
  have hnon := Complex.normSq_nonneg c
  have hw : ‖(1 : ℂ) + c * star c‖ = 1 + Complex.normSq c := by
    have hec : (1 : ℂ) + c * star c = ((1 + Complex.normSq c : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
    rw [hec, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hw]
  have hcn : 1 + Complex.normSq c ≠ 0 := by positivity
  field_simp

theorem sphericalDeriv_reciprocal (F : ℂ → RiemannSphere) (a : ℂ)
    (hf : PlaneSphereHolomorphicAt F a) :
    sphericalDeriv (reciprocal ∘ F) a = sphericalDeriv F a := by
  obtain ⟨u, v, hu, hv, ha, he⟩ := local_pair F a hf
  have hn : ∀ᶠ z in 𝓝 a, u z ≠ 0 ∨ v z ≠ 0 := by
    rcases ha with ha | ha
    · exact (hu.differentiableAt.continuousAt.eventually_ne ha).mono (fun _ h => Or.inl h)
    · exact (hv.differentiableAt.continuousAt.eventually_ne ha).mono (fun _ h => Or.inr h)
  have he' : (reciprocal ∘ F) =ᶠ[𝓝 a]
      (fun z => Mobius.spherePair (v z) (u z)) := by
    filter_upwards [he, hn] with z hz hnz
    rw [Function.comp_apply, hz, reciprocal, Mobius.mobiusMap_pair _ _ _ hnz]
    simp
  rw [sphericalDeriv_congr he', sphericalDeriv_congr he,
    sphericalDeriv_pair _ _ a hv.differentiableAt hu.differentiableAt ha.symm,
    sphericalDeriv_pair _ _ a hu.differentiableAt hv.differentiableAt ha]
  rw [show deriv v a * u a - v a * deriv u a =
    -(deriv u a * v a - u a * deriv v a) by ring, norm_neg, add_comm]

theorem differentiable_finiteStereographic : Differentiable ℝ finiteStereographic := by
  intro w
  apply (differentiableAt_piLp (p := (2 : ENNReal))).mpr
  intro i
  fin_cases i <;> dsimp [finiteStereographic]
  all_goals simp only [Complex.sq_norm, Complex.normSq_apply]
  all_goals fun_prop (disch := nlinarith [sq_nonneg w.re, sq_nonneg w.im])

/-- In reciprocal coordinates, stereographic projection is a reflection in
its second and third coordinates. The formula is valid at zero as well. -/
theorem stereographic_infinityParametrization (w : ℂ) :
    stereographic (infinityParametrization w) =
      WithLp.toLp 2 ![2 * w.re / (1 + ‖w‖ ^ 2),
        -(2 * w.im / (1 + ‖w‖ ^ 2)), -((‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2))] := by
  by_cases hw : w = 0
  · subst w
    ext i
    fin_cases i <;> norm_num [infinityParametrization, stereographic, northPole, sphereInfty]
  · rw [infinityParametrization_ne_zero w hw]
    apply PiLp.ext
    intro i
    fin_cases i <;> dsimp [stereographic, finiteStereographic, sphereFinite]
    all_goals
      simp only [Complex.inv_re, Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
      have hn := (Complex.normSq_pos.mpr hw).ne'
      have hnon := Complex.normSq_nonneg w
      have hn' : 1 + Complex.normSq w ≠ 0 := by positivity
      field_simp
      ring

theorem differentiable_reciprocalStereographic :
    Differentiable ℝ (fun w => stereographic (infinityParametrization w)) := by
  simp_rw [stereographic_infinityParametrization]
  intro w
  apply (differentiableAt_piLp (p := (2 : ENNReal))).mpr
  intro i
  fin_cases i <;> dsimp
  all_goals simp only [Complex.sq_norm, Complex.normSq_apply]
  all_goals fun_prop (disch := nlinarith [sq_nonneg w.re, sq_nonneg w.im])

/-- Differentiate an actual Euclidean curve, then compute the norm of its
velocity from the previously proved exact chord-distance formula. -/
theorem line_element_of_chordal (e : ℂ → RiemannSphere)
    (he : ∀ x y, chordal (e x) (e y) = chordal (sphereFinite x) (sphereFinite y))
    (w v : ℂ)
    (hd : DifferentiableAt ℝ (fun t : ℝ => stereographic (e (w + t • v))) 0) :
    ∃ V : Euclidean3,
      HasDerivAt (fun t : ℝ => stereographic (e (w + t • v))) V 0 ∧
      ‖V‖ = 2 * ‖v‖ / (1 + ‖w‖ ^ 2) := by
  let P : ℝ → Euclidean3 := fun t => stereographic (e (w + t • v))
  refine ⟨deriv P 0, hd.hasDerivAt, ?_⟩
  have hs := hd.hasDerivAt.tendsto_slope_zero.norm
  have hlim : Tendsto (fun t : ℝ => 2 * ‖v‖ / (weight (w + t • v) * weight w))
      (𝓝[≠] 0) (𝓝 (2 * ‖v‖ / (1 + ‖w‖ ^ 2))) := by
    have hc : ContinuousAt (fun t : ℝ => 2 * ‖v‖ / (weight (w + t • v) * weight w)) 0 := by
      unfold weight
      fun_prop (disch := positivity)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa only [zero_smul, add_zero, ← pow_two, weight_sq] using ht
  apply tendsto_nhds_unique hs
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  change 2 * ‖v‖ / (weight (w + t • v) * weight w) =
    ‖t⁻¹ • (P (0 + t) - P 0)‖
  simp only [norm_smul, norm_inv]
  have hc := chordal_half_chord (e (w + t • v)) (e w)
  rw [he, chordal_finite, dist_eq_norm] at hc
  simp only [add_sub_cancel_left] at hc
  change ‖t • v‖ / (weight (w + t • v) * weight w) = _ at hc
  have hn : ‖P (0 + t) - P 0‖ =
      2 * (‖t‖ * ‖v‖ / (weight (w + t • v) * weight w)) := by
    simpa only [P, zero_add, zero_smul, add_zero, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs] using (show
        ‖stereographic (e (w + t • v)) - stereographic (e w)‖ =
          2 * (‖t • v‖ / (weight (w + t • v) * weight w)) by linarith [hc])
  rw [hn]
  have hnt : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht0
  field_simp

theorem stereographic_line_element (w v : ℂ) :
    ∃ V : Euclidean3,
      HasDerivAt (fun t : ℝ => stereographic (sphereFinite (w + t • v))) V 0 ∧
      ‖V‖ = 2 * ‖v‖ / (1 + ‖w‖ ^ 2) := by
  apply line_element_of_chordal sphereFinite (fun _ _ => rfl) w v
  change DifferentiableAt ℝ (fun t : ℝ => finiteStereographic (w + t • v)) 0
  have hd : DifferentiableAt ℝ (fun t : ℝ => w + t • v) 0 := by fun_prop
  have hh := (differentiable_finiteStereographic (w + (0 : ℝ) • v)).comp 0 hd
  exact hh

theorem reciprocal_finite (w : ℂ) : reciprocal (sphereFinite w) = infinityParametrization w := by
  simp [reciprocal, Mobius.mobiusMap, Mobius.spherePair, infinityParametrization, sphereFinite,
    div_eq_mul_inv]

theorem reciprocal_line_element (w v : ℂ) :
    ∃ V : Euclidean3,
      HasDerivAt (fun t : ℝ => stereographic (infinityParametrization (w + t • v))) V 0 ∧
      ‖V‖ = 2 * ‖v‖ / (1 + ‖w‖ ^ 2) := by
  have he : ∀ x y, chordal (infinityParametrization x) (infinityParametrization y) =
      chordal (sphereFinite x) (sphereFinite y) := by
    intro x y
    rw [← reciprocal_finite, ← reciprocal_finite, reciprocal_chordal]
  apply line_element_of_chordal infinityParametrization he w v
  have hd : DifferentiableAt ℝ (fun t : ℝ => w + t • v) 0 := by fun_prop
  exact (differentiable_reciprocalStereographic (w + (0 : ℝ) • v)).comp 0 hd

end D12Complex.SphericalDerivative
