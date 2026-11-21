import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.GreenSymmetry
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CanonicalGreen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.TruncatedGreenIdentity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff

namespace D12Complex.GreenSymmetry
open CircularExhaustion TruncatedGreenIdentity

lemma fderiv_log_norm_sub (a z w : ℂ) (hz : z ≠ a) :
    fderiv ℝ (fun y : ℂ => Real.log ‖y - a‖) z w =
      (‖z - a‖ ^ 2)⁻¹ * inner ℝ (z-a) w := by
  have hn : ‖z-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  have hd := (((hasFDerivAt_id z).sub_const a).norm_sq).log (pow_ne_zero 2 hn)
  simp only [id_eq] at hd
  have heq : (fun y : ℂ => Real.log ‖y-a‖) = fun y => (2:ℝ)⁻¹ * Real.log (‖y-a‖^2) := by
    funext y
    rw [Real.log_pow]
    ring
  rw [heq, (hd.const_mul ((2:ℝ)⁻¹)).fderiv]
  simp
  ring

lemma log_differentiableAt (a z : ℂ) (hz : z ≠ a) :
    DifferentiableAt ℝ (fun y : ℂ => Real.log ‖y-a‖) z := by
  exact (((differentiableAt_id.sub_const a).norm ℝ (sub_ne_zero.mpr hz)).log
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))

lemma inner_gradient_log_normal (a : ℂ) (r t : ℝ) (hr : 0 < r) :
    inner ℝ (gradient (fun y : ℂ => Real.log ‖y-a‖) (arcParam a r t))
      (inwardCircleNormal t) = -r⁻¹ := by
  have hn := norm_arcParam_sub a r t hr.le
  have hza : arcParam a r t ≠ a := by
    intro he
    simp [he] at hn
    linarith
  rw [inner_gradient_left, fderiv_log_norm_sub a _ _ hza, hn]
  have hi : inner ℝ (arcParam a r t - a) (inwardCircleNormal t) = -r := by
    simp only [arcParam, add_sub_cancel_left, inwardCircleNormal]
    rw [← Complex.real_smul, real_inner_smul_left, inner_neg_right]
    simp [Complex.norm_exp]
  rw [hi]
  field_simp

lemma circle_density_model {D : Set ℂ} {a : ℂ} {u h v : ℂ → ℝ}
    {R r : ℝ} (hR : 0 < R) (hD : ball a R ⊆ D)
    (hh : DifferentiableOn ℝ h (ball a R))
    (heq : EqOn h (fun z => u z + Real.log ‖z-a‖) (ball a R \ {a}))
    (hr : 0 < r) (hrR : r < R) (t : ℝ) :
    circleFluxIntegrand D u v a r t =
      (h (arcParam a r t) * r - r * Real.log r) *
        inner ℝ (gradient v (arcParam a r t)) (inwardCircleNormal t) -
      (v (arcParam a r t) * r) *
        inner ℝ (gradient h (arcParam a r t)) (inwardCircleNormal t) -
      v (arcParam a r t) := by
  let z := arcParam a r t
  have hn : ‖z-a‖ = r := norm_arcParam_sub a r t hr.le
  have hz : z ∈ ball a R := by simpa [mem_ball, dist_eq_norm, hn] using hrR
  have hza : z ≠ a := by intro he; simp [he] at hn; linarith
  have hnhds : ball a R \ {a} ∈ 𝓝 z :=
    (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz,hza⟩
  have heu : u =ᶠ[𝓝 z] (fun w => h w - Real.log ‖w-a‖) := by
    filter_upwards [hnhds] with w hw
    have := heq hw
    linarith
  have huval : u z = h z - Real.log r := by
    simpa [hn] using heu.eq_of_nhds
  have hgrad : gradient u z = gradient h z - gradient (fun w : ℂ => Real.log ‖w-a‖) z := by
    rw [heu.gradient_eq]
    apply ext_inner_right ℝ
    intro w
    simp only [inner_sub_left, inner_gradient_left]
    exact congrArg (fun L : ℂ →L[ℝ] ℝ => L w)
      (((hh z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasFDerivAt.sub
        (log_differentiableAt a z hza).hasFDerivAt).fderiv
  have hi : inner ℝ (gradient u z) (inwardCircleNormal t) =
      inner ℝ (gradient h z) (inwardCircleNormal t) + r⁻¹ := by
    rw [hgrad, inner_sub_left, inner_gradient_log_normal a r t hr]
    ring
  change (if z ∈ D then normalFlux u v z (inwardCircleNormal t) * r else 0) = _
  rw [if_pos (hD hz)]
  unfold normalFlux
  rw [huval, hi]
  change _ = (h z * r - r * Real.log r) * _ - (v z * r) * _ - v z
  field_simp
  ring

lemma smooth_extension_ball {a : ℂ} {R : ℝ} {u : ℂ → ℝ}
    (hR : 0 < R) (hu : ContDiffOn ℝ ∞ u (ball a R)) :
    ∃ u₀ : ℂ → ℝ, ContDiff ℝ ∞ u₀ ∧ EqOn u₀ u (ball a (R/2)) := by
  have hloc : ∀ z ∈ closedBall a (R/2),
      ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℝ,
        ContDiffOn ℝ ∞ g U ∧ EqOn g u (closedBall a (R/2) ∩ U) := by
    intro z hz
    have hsub : closedBall a (R/2) ⊆ ball a R :=
      closedBall_subset_ball (by linarith)
    exact ⟨ball a R, isOpen_ball, hsub hz, u, hu, fun _ _ => rfl⟩
  obtain ⟨u₀, hu₀, heq⟩ := exists_smooth_extension_of_locally
    (isClosed_closedBall : IsClosed (closedBall a (R/2))) u hloc
  exact ⟨u₀, hu₀, heq.mono ball_subset_closedBall⟩

def modelDensity (a : ℂ) (h v : ℂ → ℝ) (r t : ℝ) : ℝ :=
  (h (arcParam a r t) * r - r * Real.log r) *
    inner ℝ (gradient v (arcParam a r t)) (inwardCircleNormal t) -
  (v (arcParam a r t) * r) *
    inner ℝ (gradient h (arcParam a r t)) (inwardCircleNormal t) -
  v (arcParam a r t)

lemma continuous_gradient_of_contDiff {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) :
    Continuous (gradient h) := by
  have hd := (hh.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).continuous_fderiv (by norm_num)
  exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp hd

lemma continuous_modelDensity (a : ℂ) {h v : ℂ → ℝ}
    (hh : ContDiff ℝ 2 h) (hv : ContDiff ℝ 2 v) :
    Continuous (Function.uncurry (modelDensity a h v)) := by
  have hA : Continuous (fun p : ℝ × ℝ => arcParam a p.1 p.2) := by
    unfold arcParam
    fun_prop
  have hN : Continuous (fun p : ℝ × ℝ => inwardCircleNormal p.2) := by
    unfold inwardCircleNormal
    fun_prop
  have hhc := hh.continuous.comp hA
  have hvc := hv.continuous.comp hA
  have hhg := (continuous_gradient_of_contDiff hh).comp hA
  have hvg := (continuous_gradient_of_contDiff hv).comp hA
  have hlog : Continuous (fun p : ℝ × ℝ => p.1 * Real.log p.1) :=
    Real.continuous_mul_log.comp continuous_fst
  exact (((hhc.mul continuous_fst).sub hlog).mul (hvg.inner hN)).sub
    ((hvc.mul continuous_fst).mul (hhg.inner hN)) |>.sub hvc

lemma modelIntegral_tendsto (a : ℂ) {h v : ℂ → ℝ}
    (hh : ContDiff ℝ 2 h) (hv : ContDiff ℝ 2 v) :
    Tendsto (fun r => ∫ t in (0:ℝ)..(2 * Real.pi), modelDensity a h v r t)
      (𝓝 0) (𝓝 (-2 * Real.pi * v a)) := by
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (continuous_modelDensity a hh hv) 0 (2 * Real.pi)
  have hzero : (∫ t in (0:ℝ)..(2 * Real.pi), modelDensity a h v 0 t) =
      -2 * Real.pi * v a := by
    simp [modelDensity, arcParam]
  simpa only [hzero] using hcont.tendsto 0

lemma normalized_pole_circle_flux (D : Set ℂ) (a : ℂ) (u v : ℂ → ℝ)
    (_hD : IsOpen D) (_ha : a ∈ D) (hu : NormalizedPole D a u)
    (hvnear : ∃ R : ℝ, 0 < R ∧ HarmonicOn (ball a R) v) :
    Tendsto (circleFlux D u v a) (𝓝[>] 0) (𝓝 (-2 * Real.pi * v a)) := by
  obtain ⟨Rh, hRh, hRhD, h, hh, heq⟩ := hu.2.2.2
  obtain ⟨Rv, hRv, hv⟩ := hvnear
  let R : ℝ := min Rh Rv
  have hR : 0 < R := lt_min hRh hRv
  have hRRh : R ≤ Rh := min_le_left _ _
  have hRRv : R ≤ Rv := min_le_right _ _
  have hhR : ContDiffOn ℝ ∞ h (ball a R) :=
    (LocalConjugateRegularity.harmonic_smooth _ _ hh).mono (ball_subset_ball hRRh)
  have hvR : ContDiffOn ℝ ∞ v (ball a R) :=
    (LocalConjugateRegularity.harmonic_smooth _ _ hv).mono (ball_subset_ball hRRv)
  obtain ⟨h₀, hh₀, heqh₀⟩ := smooth_extension_ball hR hhR
  obtain ⟨v₀, hv₀, heqv₀⟩ := smooth_extension_ball hR hvR
  have hRhalf : 0 < R/2 := half_pos hR
  have hhalfRh : R/2 ≤ Rh := by linarith
  have hhalfD : ball a (R/2) ⊆ D := (ball_subset_ball hhalfRh).trans hRhD
  have hcorrection : EqOn h₀ (fun z => u z + Real.log ‖z-a‖)
      (ball a (R/2) \ {a}) := by
    intro z hz
    exact (heqh₀ hz.1).trans (heq z ⟨ball_subset_ball hhalfRh hz.1, hz.2⟩)
  have hmodel := (modelIntegral_tendsto a (hh₀.of_le (by norm_num))
    (hv₀.of_le (by norm_num))).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hva : v₀ a = v a := heqv₀ (mem_ball_self hRhalf)
  rw [hva] at hmodel
  apply hmodel.congr' ?_
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < R/2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds hRhalf)] with r hr hrR
    exact ⟨hr, hrR⟩
  filter_upwards [hsmall] with r hr
  unfold circleFlux
  apply intervalIntegral.integral_congr
  intro t _
  have hz : arcParam a r t ∈ ball a (R/2) := by
    simpa [mem_ball, dist_eq_norm, norm_arcParam_sub a r t hr.1.le] using hr.2
  have hg : gradient v₀ (arcParam a r t) = gradient v (arcParam a r t) :=
    eqOn_gradient_on_open isOpen_ball heqv₀ hz
  rw [circle_density_model hRhalf hhalfD (hh₀.differentiable (by norm_num)).differentiableOn
    hcorrection hr.1 hr.2 t]
  simp only [modelDensity, heqv₀ hz, hg]


/-- The two canonical formulations of a normalized zero-boundary pole agree. -/
lemma normalizedPole_of_zeroBoundary {D : Set ℂ} {a : ℂ} {u : ℂ → ℝ}
    (hu : IsZeroBoundaryGreen D a u) : NormalizedPole D a u := by
  exact ⟨hu.1, hu.2.2.1, hu.2.2.2, hu.2.1⟩

lemma harmonic_near_other_pole {D : Set ℂ} {a b : ℂ} {v : ℂ → ℝ}
    (hD : IsOpen D) (ha : a ∈ D) (hab : a ≠ b)
    (hv : HarmonicOn (D \ {b}) v) :
    ∃ R : ℝ, 0 < R ∧ HarmonicOn (ball a R) v := by
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp (hD.sdiff isClosed_singleton)
    a ⟨ha, hab⟩
  exact ⟨R, hR, HarmonicRemovable.harmonicOn_mono hv isOpen_ball hsub⟩

lemma circleFlux_swap (D : Set ℂ) (u v : ℂ → ℝ) (a : ℂ) (r : ℝ) :
    circleFlux D u v a r = -circleFlux D v u a r := by
  unfold circleFlux
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  by_cases hz : arcParam a r t ∈ D
  · simp only [circleFluxIntegrand, normalFlux, if_pos hz]
    ring
  · simp only [circleFluxIntegrand, normalFlux, if_neg hz, neg_zero]

/-- The fixed-cut identity, followed by the corner limit and the two pole
limits, proves symmetry for any pair of normalized zero-boundary poles. -/
lemma normalized_poles_symmetric_of_flux
    (hflux : Specs.D12Complex.Ch14.GreenSymmetry.normalized_pole_circle_flux_type)
    (Ω : Set ℂ) (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ)
    (he : IsCircularExhaustion Ω s r) (j : ℕ)
    (a b : ℂ) (u v : ℂ → ℝ)
    (ha : a ∈ diskUnion (s j) (r j)) (hb : b ∈ diskUnion (s j) (r j))
    (hab : a ≠ b) (hu : NormalizedPole (diskUnion (s j) (r j)) a u)
    (hv : NormalizedPole (diskUnion (s j) (r j)) b v) : u b = v a := by
  let D := diskUnion (s j) (r j)
  have hD : IsOpen D := (he.1 j).2.1.2.1
  obtain ⟨corners, hcorn⟩ := (he.1 j).2.2.2.2.2.2.1
  have ht₁ := hflux D a u v hD ha hu (harmonic_near_other_pole hD ha hab hv.1)
  have ht₂' := (hflux D b v u hD hb hv
    (harmonic_near_other_pole hD hb hab.symm hu.1)).neg
  have ht₂ : Tendsto (circleFlux D u v b) (𝓝[>] 0) (𝓝 (2 * Real.pi * u b)) := by
    have he : -(-2 * Real.pi * u b) = 2 * Real.pi * u b := by ring
    rw [he] at ht₂'
    exact ht₂'.congr' (Eventually.of_forall (fun t => (circleFlux_swap D u v b t).symm))
  have htc := normalized_pole_corner_flux_sum D corners hD hcorn a b u v ha hb hu hv
    (fun _ t => t) (fun _ _ => tendsto_id)
  have ht := (ht₁.add ht₂).add htc
  obtain ⟨δ, hδ, hcut⟩ := truncated_green_identity Ω s r he j corners hcorn a b u v
    ha hb hab hu hv
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      circleFlux D u v a t + circleFlux D u v b t +
        ∑ c ∈ corners, circleFlux D u v c t = 0 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with t htpos htδ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hz⟩ := hcut t t (fun _ => t)
      htpos htδ htpos htδ (fun _ _ => ⟨htpos, htδ⟩)
    exact hz
  have heq : -2 * Real.pi * v a + 2 * Real.pi * u b + 0 = 0 :=
    tendsto_nhds_unique_of_eventuallyEq ht tendsto_const_nhds hev
  nlinarith [Real.pi_pos]

lemma circular_stage_green_symmetry_of_flux
    (hflux : Specs.D12Complex.Ch14.GreenSymmetry.normalized_pole_circle_flux_type) :
    Specs.D12Complex.Ch14.GreenSymmetry.circular_stage_green_symmetry_type := by
  intro Ω s r he j a b ha hb hab
  have hD := (he.1 j).2.1
  have hDb := (he.1 j).2.2.1.isBounded.subset subset_closure
  have hreg := (he.1 j).2.2.2.2.2.2.2.2
  have hu := RegularGreen.construction_properties hD hDb hreg ha
  have hv := RegularGreen.construction_properties hD hDb hreg hb
  exact normalized_poles_symmetric_of_flux hflux Ω s r he j a b _ _ ha hb hab
    (normalizedPole_of_zeroBoundary hu) (normalizedPole_of_zeroBoundary hv)

lemma circular_exhaustion_tail {Ω : Set ℂ} {s : ℕ → Finset ℂ} {r : ℕ → ℂ → ℝ}
    (he : IsCircularExhaustion Ω s r) (N : ℕ) :
    IsCircularExhaustion Ω (fun j => s (N + j)) (fun j => r (N + j)) := by
  have hcof : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ j, K ⊆ diskUnion (s (N + j)) (r (N + j)) := by
    intro K hK hKΩ
    obtain ⟨j, hj⟩ := he.2.2 K hK hKΩ
    exact ⟨j, hj.trans (CanonicalGreen.circular_mono he (by omega : j ≤ N + j))⟩
  refine ⟨?_, ?_, hcof⟩
  · intro j
    simpa only [Nat.add_assoc] using he.1 (N + j)
  · apply Subset.antisymm
    · exact iUnion_subset fun j => subset_closure.trans (he.1 (N + j)).2.2.2.1
    · intro z hz
      obtain ⟨j, hj⟩ := hcof {z} isCompact_singleton (singleton_subset_iff.mpr hz)
      exact mem_iUnion.mpr ⟨j, hj (mem_singleton z)⟩

lemma canonical_symmetry_of_circular_symmetry
    (hcircular : ∀ (Ω : Set ℂ) (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
      IsCircularExhaustion Ω s r → ∀ j : ℕ, ∀ a b : ℂ,
        a ∈ diskUnion (s j) (r j) → b ∈ diskUnion (s j) (r j) → a ≠ b →
        Specs.D12Complex.Ch14.RegularGreen.regularGreen_value (diskUnion (s j) (r j)) a b =
          Specs.D12Complex.Ch14.RegularGreen.regularGreen_value (diskUnion (s j) (r j)) b a)
    (Ω : Set ℂ) (a b : ℂ) (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω)
    (ha : a ∈ Ω) (hb : b ∈ Ω) (hab : a ≠ b) :
    Specs.D12Complex.Ch14.CanonicalGreen.canonicalGreen_value Ω a b =
      Specs.D12Complex.Ch14.CanonicalGreen.canonicalGreen_value Ω b a := by
  obtain ⟨s, r, he, hea⟩ := CanonicalGreen.circular_exhaustion_containing_pole Ω a hΩ ha
  obtain ⟨N, hN⟩ := he.2.2 {b} isCompact_singleton (singleton_subset_iff.mpr hb)
  let s' := fun j => s (N + j)
  let r' := fun j => r (N + j)
  have he' : IsCircularExhaustion Ω s' r' := circular_exhaustion_tail he N
  have hea' : ∀ j, a ∈ diskUnion (s' j) (r' j) := fun j => hea (N + j)
  have heb' : ∀ j, b ∈ diskUnion (s' j) (r' j) := by
    intro j
    exact CanonicalGreen.circular_mono he (Nat.le_add_right N j) (hN (mem_singleton b))
  have hca := (CanonicalGreen.exhaustion_limit Ω a hΩ hΩb ha s' r' he' hea').2
  have hcb := (CanonicalGreen.exhaustion_limit Ω b hΩ hΩb hb s' r' he' heb').2
  have hta := (hca {b} isCompact_singleton
    (singleton_subset_iff.mpr ⟨hb, hab.symm⟩)).tendsto_at (mem_singleton b)
  have htb := (hcb {a} isCompact_singleton
    (singleton_subset_iff.mpr ⟨ha, hab⟩)).tendsto_at (mem_singleton a)
  exact tendsto_nhds_unique_of_eventuallyEq hta htb
    (Eventually.of_forall fun j => hcircular Ω s' r' he' j a b (hea' j) (heb' j) hab)

/-- Symmetry on the regular circular exhaustion stages, using the fixed-cut
second Green identity and the normalized pole limits. -/
theorem circular_stage_green_symmetry :
    Specs.D12Complex.Ch14.GreenSymmetry.circular_stage_green_symmetry_type :=
  circular_stage_green_symmetry_of_flux normalized_pole_circle_flux

/-- The canonical positive Green function is symmetric on every bounded domain.
No boundary regularity assumption is imposed on the original domain. -/
theorem canonical_green_symmetry :
    Specs.D12Complex.Ch14.GreenSymmetry.canonical_green_symmetry_type := by
  exact canonical_symmetry_of_circular_symmetry circular_stage_green_symmetry

end D12Complex.GreenSymmetry
