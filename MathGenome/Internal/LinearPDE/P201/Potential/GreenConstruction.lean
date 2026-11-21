import MathGenome.Internal.LinearPDE.P201Specs.Potential.GreenConstruction
import MathGenome.Internal.LinearPDE.P201.Potential.Fundamental
import MathGenome.Internal.LinearPDE.P201.Potential.Weyl
import MathGenome.Internal.LinearPDE.P201.Potential.SubharmonicMaximum
import MathGenome.Internal.LinearPDE.P201.Common.NormalTrace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Homeomorph.Lemmas
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionConvolution
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import MathGenome.Internal.LinearPDE.P201.Potential.SmoothHarmonicLift
/-! Conditional derivation of the full Green construction. The harmonic
lifting theorem is an explicit parameter, never an imported proof. The public
helper `construction_conditional` proves the original specification under that
premise; the original target name is reserved for later dependency closure. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace P201.GreenConstruction
open P201Specs
open P201Specs.GreenConstruction

theorem intervalKernel_symmetric (a b x y : ℝ) :
    intervalKernel a b x y = intervalKernel a b y x := by
  simp only [intervalKernel, min_comm x y, max_comm x y]

theorem intervalKernel_left {a b x y : ℝ} (h : y ≤ x) :
    intervalKernel a b x y = (y - a) * (b - x) / (b - a) := by
  simp [intervalKernel, min_eq_right h, max_eq_left h]

theorem intervalKernel_right {a b x y : ℝ} (h : x ≤ y) :
    intervalKernel a b x y = (x - a) * (b - y) / (b - a) := by
  simp [intervalKernel, min_eq_left h, max_eq_right h]

theorem intervalKernel_endpoints {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    intervalKernel a b x a = 0 ∧ intervalKernel a b x b = 0 := by
  rw [intervalKernel_left hax, intervalKernel_right hxb]
  simp

theorem intervalKernel_positive {a b x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    0 < intervalKernel a b x y := by
  unfold intervalKernel
  exact div_pos (mul_pos (sub_pos.mpr (lt_min hx.1 hy.1))
    (sub_pos.mpr (max_lt hx.2 hy.2))) (sub_pos.mpr (hx.1.trans hx.2))

theorem intervalKernel_continuous (a b x : ℝ) : Continuous (intervalKernel a b x) := by
  unfold intervalKernel
  fun_prop

theorem intervalKernel_slopes {a b x : ℝ} (hx : x ∈ Ioo a b) :
    HasIntervalSlopes a b x := by
  have hab : b - a ≠ 0 := ne_of_gt (sub_pos.mpr (hx.1.trans hx.2))
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have he : intervalKernel a b x =ᶠ[𝓝 t]
        (fun s : ℝ => (s - a) * (b - x) / (b - a)) := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      exact intervalKernel_left hs.le
    simpa only [one_mul] using
      ((((hasDerivAt_id t).sub_const a).mul_const (b - x)).div_const (b - a)).congr_of_eventuallyEq he
  · intro t ht
    have he : intervalKernel a b x =ᶠ[𝓝 t]
        (fun s : ℝ => (x - a) * (b - s) / (b - a)) := by
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      exact intervalKernel_right hs.le
    convert (((hasDerivAt_const t b).sub (hasDerivAt_id t)).const_mul (x - a)).div_const
      (b - a) |>.congr_of_eventuallyEq he using 1; ring
  · field_simp
    ring

/-- Off the pole the exact normalized kernel is smooth, including the
logarithmic two-dimensional case. No distributional identity is assumed. -/
theorem fundamental_contDiffAt {n : ℕ} {z : Space n} (hz : z ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fundamentalKernel n) z := by
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => ‖y‖) z :=
    contDiffAt_norm ℝ hz
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => P201Specs.fundamentalProfile n ‖y‖) z
  unfold P201Specs.fundamentalProfile
  split_ifs with h1 h2
  · exact hnorm.neg.div_const 2
  · exact contDiffAt_const.mul (hnorm.log hnz)
  · exact (hnorm.rpow_const_of_ne hnz).div_const _

theorem translated_fundamental_contDiffAt {n : ℕ} (x : Space n)
    {y : Space n} (hy : y ≠ x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => fundamentalKernel n (z - x)) y := by
  exact ContDiffAt.comp (f := fun z : Space n => z - x) (g := fundamentalKernel n) y
    (fundamental_contDiffAt (sub_ne_zero.mpr hy)) (contDiffAt_id.sub contDiffAt_const)

/-- Multiplying by a cutoff which vanishes near the pole produces an actual
globally smooth lift of the boundary values. Its construction only uses that
the pole lies in the open set; no boundary regularity is needed here. -/
theorem smooth_boundary_lift {n : ℕ} (Ω : Domain n) {x : Space n} (hx : x ∈ Ω) :
    ∃ F : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ z ∈ frontier (Ω : Set _), F z = fundamentalKernel n (z - x) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  let β : ContDiffBump x := ⟨ε / 2, ε, by positivity, by linarith⟩
  let F := fun z => (1 - β z) * fundamentalKernel n (z - x)
  refine ⟨F, contDiff_iff_contDiffAt.mpr (fun z => ?_), ?_⟩
  · by_cases hz : z = x
    · subst z
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [β.eventuallyEq_one] with z hz
      simp [F, hz]
    · exact (contDiffAt_const.sub β.contDiffAt).mul
        (translated_fundamental_contDiffAt x hz)
  · intro z hz
    have hzΩ : z ∉ Ω := fun h =>
      Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr Ω.isOpen) hz h
    have hdist : ε ≤ dist z x := le_of_not_gt fun h => hzΩ (hball h)
    have hβ : β z = 0 := β.zero_of_le_dist hdist
    simp [F, hβ]

/-- Conditional construction of the harmonic H² correction. The sole
conditional premise is precisely the complete frozen upstream Prop type. -/
theorem harmonic_correction_conditional
    (harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (hm : 1 ≤ m) (Ω : Domain (m + 1))
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasCkBoundary Ω 2) {x : Space (m + 1)} (hx : x ∈ Ω) :
    ∃ h : Space (m + 1) → ℝ,
      MeanValues.IsHarmonic Ω h ∧ ContinuousOn h (closure (Ω : Set _)) ∧
      (∀ z ∈ frontier (Ω : Set _), h z = fundamentalKernel (m + 1) (z - x)) ∧
      ∃ w : H ℝ Ω 2,
        (hUnderlying Ω 2 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] h := by
  obtain ⟨F, hF, hFboundary⟩ := smooth_boundary_lift Ω hx
  let g : C(frontier (Ω : Set (Space (m + 1))), ℝ) :=
    ⟨fun z => F z, hF.continuous.comp continuous_subtype_val⟩
  obtain ⟨h, hext, _, hsmooth⟩ := harmonic_lift hm Ω hbounded hboundary g
  obtain ⟨_, _, _, hw, _⟩ := hsmooth F
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ (fun _ => rfl)
  refine ⟨h, hext.1, hext.2.1, ?_, hw⟩
  intro z hz
  exact (hext.2.2 ⟨z, hz⟩).trans (hFboundary z hz)

/-- Translation preserves local integrability for the actual Euclidean
Lebesgue measure; this is the bridge from a pole at zero to an arbitrary pole. -/
theorem translated_fundamental_locallyIntegrable {n : ℕ} (hn : 1 ≤ n) (x : Space n) :
    LocallyIntegrable (fun y => fundamentalKernel n (y - x)) volume := by
  have hm : Measure.map (Homeomorph.addRight (-x)) volume = (volume : Measure (Space n)) :=
    (measurePreserving_add_right volume (-x)).map_eq
  have h := P201.fundamentalLocalIntegrability n hn
  rw [← hm] at h
  have h' := (locallyIntegrable_map_homeomorph
    (Homeomorph.addRight (-x)) (μ := (volume : Measure (Space n)))).mp h
  change LocallyIntegrable (fun y => fundamentalKernel n (y + -x)) volume at h'
  simpa only [sub_eq_add_neg] using h'

/-- Promotion of a compact test on Ω to the whole space preserves its ambient
values; compact support was already strictly inside Ω. -/
private def wholeTest {n : ℕ} {Ω : Domain n} (φ : Test ℝ Ω) : Test ℝ (⊤ : Domain n) :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩

theorem laplacian_additionTest {n : ℕ} (φ : Test ℝ (⊤ : Domain n))
    (x y : Space n) :
    laplacian (P102.U4.additionTest φ x) y = laplacian φ (x + y) := by
  apply Finset.sum_congr rfl
  intro i _
  change P102.U4.partialWord (fun z => φ (x + z))
    (({i, i} : MultiIndex n).sort (· ≤ ·)) y = _
  rw [P102.U4.partialWord_const_add φ.contDiff]
  rfl

/-- The sign and normalization are retained after moving the pole. This uses
the proved fundamental pairing, not a newly assumed source identity. -/
theorem translated_fundamental_pairing {n : ℕ} (hn : 1 ≤ n) (x : Space n)
    {Ω : Domain n} (φ : Test ℝ Ω) :
    (∫ y, fundamentalKernel n (y - x) * laplacian φ y) = -φ x := by
  have h := P201.fundamental_pairing hn (P102.U4.additionTest (wholeTest φ) x)
  simp_rw [laplacian_additionTest] at h
  change (∫ y, fundamentalKernel n y * laplacian φ (x + y)) = -φ (x + 0) at h
  have he := integral_add_left_eq_self (μ := volume)
    (fun y : Space n => fundamentalKernel n (y - x) * laplacian φ y) x
  simp only [add_sub_cancel_left] at he
  rw [← he]
  simpa only [add_zero] using h

theorem laplacian_distribution_apply {n : ℕ} {Ω : Domain n}
    (U : Distribution ℝ Ω) (φ : Test ℝ Ω) :
    distributionLaplacian U φ = ∑ i : Fin n, U (P102.U4.testPartialWord Ω [i, i] φ) := by
  simp [P201Specs.distributionDerivative,
    P102.U4.distributionPartial, Multiset.sort_cons]

theorem regular_laplacian_pairing {n : ℕ} (Ω : Domain n) (f : Space n → ℝ)
    (hf : LocallyIntegrableOn f Ω volume) (φ : Test ℝ Ω) :
    distributionLaplacian (regularDistribution Ω f) φ = ∫ y, f y * laplacian φ y := by
  rw [laplacian_distribution_apply]
  simp_rw [P201.Weyl.regular_apply Ω f hf]
  have hi (i : Fin n) : Integrable
      (fun y => f y * P102.U4.testPartialWord Ω [i, i] φ y) volume := by
    have h := (P102.U4.testPartialWord Ω [i, i] φ).integrable_bilin
      (ContinuousLinearMap.mul ℝ ℝ) hf
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using h
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  funext y
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [P102.U4.testPartialWord_coe]
  congr 1
  simp [P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_cons]

/-- The normalized distribution equation at every pole, on every open set.
The pole may even be outside Ω (when evaluation on its tests is zero). -/
theorem translated_fundamental_solution {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (x : Space n) :
    -distributionLaplacian (regularDistribution Ω
      (fun y => fundamentalKernel n (y - x))) = poleDirac Ω x := by
  ext φ
  change -distributionLaplacian (regularDistribution Ω
    (fun y => fundamentalKernel n (y - x))) φ = φ x
  rw [regular_laplacian_pairing Ω _
    ((translated_fundamental_locallyIntegrable hn x).locallyIntegrableOn _),
    translated_fundamental_pairing hn x φ, neg_neg]

theorem poleDirac_outside {n : ℕ} {Ω : Domain n} {x : Space n} (hx : x ∉ Ω) :
    poleDirac Ω x = 0 := by
  ext φ
  exact φ.zero_on_compl hx

/-- The normalized fundamental solution is classically harmonic away from
its pole. Weyl's lemma is applied to the actual restricted distribution and
pointwise uniqueness identifies its continuous representative. -/
theorem translated_fundamental_harmonic {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (x : Space n) :
    MeanValues.IsHarmonic (punctured Ω x) (fun y => fundamentalKernel n (y - x)) := by
  let V := punctured Ω x
  let f := fun y => fundamentalKernel n (y - x)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f V := fun y hy =>
    (translated_fundamental_contDiffAt x (by simpa using hy.2)).contDiffWithinAt
  have heq : distributionLaplacian (regularDistribution V f) = 0 := by
    have h := translated_fundamental_solution hn V x
    rw [poleDirac_outside (by simp [V, punctured])] at h
    exact neg_eq_zero.mp h
  obtain ⟨u, _, hu, hurep, _⟩ := P201.Weyl.weyl hn V (regularDistribution V f) heq
  have he : EqOn f u V := P201.Weyl.continuous_representative_unique V f u
    hf.continuousOn hu.1.continuousOn hurep.symm
  refine ⟨hf.of_le (by simp), fun y hy => ?_⟩
  change laplacian f y = 0
  rw [P201.Weyl.laplacian_eq_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds hy) he)]
  exact hu.2 y hy

/-- For C² functions the distributional and coordinate Laplacians agree on
the original open set, with no boundary differentiability assumptions. -/
theorem classical_laplacian_distribution {n : ℕ} (Ω : Domain n) (f : Space n → ℝ)
    (hf : ContDiffOn ℝ 2 f Ω) :
    distributionLaplacian (regularDistribution Ω f) = regularDistribution Ω (laplacian f) := by
  have hl : LocallyIntegrableOn (laplacian f) Ω volume :=
    (P201.MeanValues.laplacian_continuousOn Ω f hf).locallyIntegrableOn Ω.isOpen.measurableSet
  have hd (i : Fin n) : LocallyIntegrableOn (multiPartial f ({i, i} : MultiIndex n)) Ω volume := by
    have h := P102.U4.partialWord_contDiffOn Ω hf [i, i] 0 (by simp)
    simpa [P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_cons] using
      h.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  ext φ
  change (∑ i : Fin n, distributionDerivative ({i, i} : MultiIndex n)
    (regularDistribution Ω f)) φ = _
  have he (i : Fin n) : distributionDerivative ({i, i} : MultiIndex n)
      (regularDistribution Ω f) = regularDistribution Ω (multiPartial f {i, i}) :=
    P102.U4.derivative_classicalCompatibility n ℝ Ω {i, i} f (by simpa using hf)
  simp_rw [he]
  rw [sum_apply]
  simp_rw [P201.Weyl.regular_apply Ω _ (hd _)]
  rw [P201.Weyl.regular_apply Ω _ hl]
  have hi (i : Fin n) : Integrable
      (fun y => multiPartial f ({i, i} : MultiIndex n) y * φ y) volume := by
    have h := φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hd i)
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using h
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  funext y
  exact (Finset.sum_mul _ _ _).symm

theorem regular_zero (Ω : Domain n) :
    regularDistribution Ω (fun _ => (0 : ℝ)) = 0 := by
  ext φ
  rw [P201.Weyl.regular_apply Ω _ (locallyIntegrableOn_zero)]
  simp

theorem harmonic_distribution_zero {n : ℕ} (Ω : Domain n) (h : Space n → ℝ)
    (hh : MeanValues.IsHarmonic Ω h) :
    distributionLaplacian (regularDistribution Ω h) = 0 := by
  rw [classical_laplacian_distribution Ω h hh.1]
  have he : regularDistribution Ω (laplacian h) = regularDistribution Ω (fun _ => (0 : ℝ)) := by
    apply (P102.U4.regular_injectivity n ℝ Ω _ _
      ((P201.MeanValues.laplacian_continuousOn Ω h hh.1).locallyIntegrableOn Ω.isOpen.measurableSet)
      (locallyIntegrableOn_zero)).mpr
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
    exact hh.2 y hy
  rw [he, regular_zero]

theorem regular_sub {n : ℕ} (Ω : Domain n) (f h : Space n → ℝ)
    (hf : LocallyIntegrableOn f Ω volume) (hh : LocallyIntegrableOn h Ω volume) :
    regularDistribution Ω (fun y => f y - h y) =
      regularDistribution Ω f - regularDistribution Ω h := by
  ext φ
  rw [sub_apply]
  erw [P201.Weyl.regular_apply Ω _ (hf.sub hh),
    P201.Weyl.regular_apply Ω f hf, P201.Weyl.regular_apply Ω h hh]
  have hfi : Integrable (fun y => f y * φ y) volume := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hf
  have hhi : Integrable (fun y => h y * φ y) volume := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hh
  simpa only [Pi.sub_apply, sub_mul] using integral_sub hfi hhi

theorem distributionLaplacian_sub {n : ℕ} {Ω : Domain n} (U V : Distribution ℝ Ω) :
    distributionLaplacian (U - V) = distributionLaplacian U - distributionLaplacian V := by
  ext φ
  simp only [sub_apply, laplacian_distribution_apply, Finset.sum_sub_distrib]

theorem harmonic_sub {n : ℕ} (Ω : Domain n) (f h : Space n → ℝ)
    (hf : MeanValues.IsHarmonic Ω f) (hh : MeanValues.IsHarmonic Ω h) :
    MeanValues.IsHarmonic Ω (fun y => f y - h y) :=
  (P201.MeanValues.harmonic_bridge Ω _).mpr
    (((P201.MeanValues.harmonic_bridge Ω f).mp hf).sub
      ((P201.MeanValues.harmonic_bridge Ω h).mp hh))

/-- The normalized radial profile diverges positively at a pole in every
required dimension above one, with the logarithmic case treated separately. -/
theorem fundamentalProfile_tendsto {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fundamentalProfile n) (𝓝[>] 0) atTop := by
  change Tendsto (fun r => P201Specs.fundamentalProfile n r) (𝓝[>] 0) atTop
  by_cases h2 : n = 2
  · subst n
    have hc : -(1 / (2 * Real.pi)) < 0 :=
      neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
    simp only [P201Specs.fundamentalProfile, show ¬(2 : ℕ) = 1 by omega,
      ite_eq_left]
    exact
      (tendsto_const_nhds.neg_mul_atBot hc Real.tendsto_log_nhdsGT_zero)
  · have hnR : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
    have hd : 0 < ((n : ℝ) - 2) * omega n :=
      mul_pos (sub_pos.mpr hnR) (P201.MeanValues.omega_pos (by omega))
    simp only [P201Specs.fundamentalProfile,
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right h2]
    exact
      (tendsto_rpow_neg_nhdsGT_zero (show 2 - (n : ℝ) < 0 by linarith)).atTop_div_const hd

/-- Moving the pole retains positive divergence on the punctured neighborhood. -/
theorem translated_fundamental_tendsto {n : ℕ} (hn : 2 ≤ n) (x : Space n) :
    Tendsto (fun y => fundamentalKernel n (y - x)) (𝓝[≠] x) atTop := by
  have ht : Tendsto (fun y : Space n => ‖y - x‖) (𝓝[≠] x) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Pi.sub_apply, id_eq, sub_self, norm_zero] using
        ((continuous_id.sub continuous_const).norm.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds : Tendsto (fun y : Space n => ‖y - x‖) (𝓝[≠] x) (𝓝 ‖x - x‖))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hy)
  exact (fundamentalProfile_tendsto hn).comp ht

/-- Subtracting the continuous harmonic correction preserves the pole's
positive divergence. Values assigned at the single pole do not enter. -/
theorem green_tendsto_atTop {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    {x : Space n} (hx : x ∈ Ω) (g : Space n → ℝ)
    (hcorr : HasHarmonicCorrection Ω x g) :
    Tendsto g (𝓝[≠] x) atTop := by
  obtain ⟨h, _, hc, _, _, he⟩ := hcorr
  have hh : Tendsto h (𝓝[≠] x) (𝓝 (h x)) :=
    (hc.continuousAt (mem_of_superset (Ω.isOpen.mem_nhds hx) subset_closure)).tendsto.mono_left
      nhdsWithin_le_nhds
  have heq : g =ᶠ[𝓝[≠] x] (fun y => fundamentalKernel n (y - x) - h y) := by
    filter_upwards [self_mem_nhdsWithin,
      (show (Ω : Set _) ∈ 𝓝[≠] x from nhdsWithin_le_nhds (Ω.isOpen.mem_nhds hx))] with y hne hy
    exact he y ⟨subset_closure hy, hne⟩
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [heq, (translated_fundamental_tendsto hn x).eventually
    (eventually_ge_atTop (b + h x + 1)), hh.eventually
    (gt_mem_nhds (show h x < h x + 1 by linarith))] with y hy hΦ hhy
  rw [hy]
  linarith

/-- Comparison on the punctured open set. At its extra boundary point the
positive pole divergence supplies the required upper bound for the negative
Green function. No connectedness or boundary smoothness is needed. -/
theorem green_nonnegative {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hbounded : Bornology.IsBounded (Ω : Set (Space n)))
    {x : Space n} (hx : x ∈ Ω) (g : Space n → ℝ)
    (hg : IsGreenFunction Ω x g) (hcorr : HasHarmonicCorrection Ω x g) :
    ∀ y ∈ closure (Ω : Set _) \ {x}, 0 ≤ g y := by
  let V := punctured Ω x
  let u := fun y => -g y
  have hu : MeanValues.IsHarmonic V u :=
    (P201.MeanValues.harmonic_bridge V _).mpr
      (((P201.MeanValues.harmonic_bridge V g).mp hg.2.2.2.1).neg)
  have hmean := (P201.SubharmonicMaximum.smooth_extended_ball_criterion hn V u hu.1).mpr
    (fun y hy => (hu.2 y hy).ge)
  have hboundary : ∀ z ∈ frontier (V : Set _),
      limsup (fun y => (u y : EReal)) (𝓝[V] z) ≤ (0 : EReal) := by
    intro z hz
    by_cases hzx : z = x
    · subst z
      apply limsup_le_of_le (by isBoundedDefault)
      have hm : 𝓝[V] x ≤ 𝓝[≠] x := nhdsWithin_mono _ (fun y hy => hy.2)
      filter_upwards [((green_tendsto_atTop hn Ω hx g hcorr).eventually
        (eventually_ge_atTop 0)).filter_mono hm] with y hy
      exact EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr hy)
    · have hzcl : z ∈ closure (Ω : Set _) := closure_mono sdiff_subset hz.1
      have hzΩ : z ∉ Ω := by
        intro h
        exact hz.2 ((V.isOpen.interior_eq).symm ▸ (show z ∈ V from ⟨h, by simpa using hzx⟩))
      have hzfr : z ∈ frontier (Ω : Set _) := by
        rw [Ω.isOpen.frontier_eq]; exact ⟨hzcl, hzΩ⟩
      have : NeBot (𝓝[V] z) := mem_closure_iff_nhdsWithin_neBot.mp hz.1
      have ht : Tendsto (fun y => (u y : EReal)) (𝓝[V] z) (𝓝 (-g z : EReal)) :=
        continuous_coe_real_ereal.continuousAt.tendsto.comp
          ((hg.2.2.2.2.1 z ⟨hzcl, by simpa using hzx⟩).neg.mono
            (fun y hy => ⟨subset_closure hy.1, hy.2⟩))
      rw [ht.limsup_eq, hg.2.2.2.2.2 z hzfr]
      simp
  have hm := P201.SubharmonicMaximum.boundary_maximum hn V
    (fun y => (u y : EReal)) 0 (hbounded.subset sdiff_subset)
    (continuous_coe_real_ereal.comp_continuousOn hu.1.continuousOn).upperSemicontinuousOn
    (fun y _ => EReal.coe_ne_top (u y)) hmean hboundary
  intro y hy
  by_cases hyΩ : y ∈ Ω
  · exact neg_nonpos.mp (EReal.coe_le_coe_iff.mp (hm y ⟨hyΩ, hy.2⟩))
  · have hyfr : y ∈ frontier (Ω : Set _) := by
      rw [Ω.isOpen.frontier_eq]; exact ⟨hy.1, hyΩ⟩
    rw [hg.2.2.2.2.2 y hyfr]

/-- A zero away from a positive pole would form a relatively open and closed
zero region in its component. The local strong principle and pole divergence
rule this out without requiring a separate punctured-component topology lemma. -/
theorem green_positive {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hbounded : Bornology.IsBounded (Ω : Set (Space n)))
    {x : Space n} (hx : x ∈ Ω) (g : Space n → ℝ)
    (hg : IsGreenFunction Ω x g) (hcorr : HasHarmonicCorrection Ω x g) :
    ∀ y ∈ connectedComponentIn (Ω : Set _) x, x ≠ y → 0 < g y := by
  let V := punctured Ω x
  let u := fun y => -g y
  have hu : MeanValues.IsHarmonic V u :=
    (P201.MeanValues.harmonic_bridge V _).mpr
      (((P201.MeanValues.harmonic_bridge V g).mp hg.2.2.2.1).neg)
  have hmean := (P201.SubharmonicMaximum.smooth_extended_ball_criterion hn V u hu.1).mpr
    (fun y hy => (hu.2 y hy).ge)
  have husc := (continuous_coe_real_ereal.comp_continuousOn hu.1.continuousOn).upperSemicontinuousOn
  have hnonneg := green_nonnegative hn Ω hbounded hx g hg hcorr
  let A := {y | y ∈ Ω ∧ y ≠ x ∧ g y = 0}
  let B := {y | y ∈ Ω ∧ (y = x ∨ 0 < g y)}
  have hA : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyV : y ∈ V := ⟨hy.1, by simpa using hy.2.1⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (V.isOpen.mem_nhds hyV)
    have hclosed : closedBall y (r / 2) ⊆ (V : Set _) :=
      (closedBall_subset_ball (by linarith)).trans hball
    have hconst := P201.SubharmonicMaximum.ball_constant_of_max V
      (fun z => (u z : EReal)) husc hmean y (r / 2) (by linarith) hclosed 0
      (by simp [u, hy.2.2]) (fun z hz => EReal.coe_le_coe_iff.mpr
        (neg_nonpos.mpr (hnonneg z ⟨subset_closure (hclosed (ball_subset_closedBall hz)).1,
          (hclosed (ball_subset_closedBall hz)).2⟩)))
    apply Filter.mem_of_superset (ball_mem_nhds y (show 0 < r / 2 by linarith))
    intro z hz
    have hzV := hclosed (ball_subset_closedBall hz)
    refine ⟨hzV.1, by simpa using hzV.2, ?_⟩
    have he : -g z = 0 := EReal.coe_eq_coe_iff.mp (by simpa [u] using hconst z hz)
    exact neg_eq_zero.mp he
  have hB : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rcases hy.2 with hxy | hgy
    · subst y
      have hp := (green_tendsto_atTop hn Ω hx g hcorr).eventually (eventually_gt_atTop 0)
      rw [eventually_nhdsWithin_iff] at hp
      filter_upwards [Ω.isOpen.mem_nhds hx, hp] with z hz hpz
      exact ⟨hz, (eq_or_ne z x).imp_right (fun h => hpz h)⟩
    · by_cases hyx : y = x
      · have hp := (green_tendsto_atTop hn Ω hx g hcorr).eventually (eventually_gt_atTop 0)
        rw [eventually_nhdsWithin_iff] at hp
        subst y
        filter_upwards [Ω.isOpen.mem_nhds hx, hp] with z hz hpz
        exact ⟨hz, (eq_or_ne z x).imp_right (fun h => hpz h)⟩
      · have hyV : y ∈ V := ⟨hy.1, by simpa using hyx⟩
        have hgc := hg.2.2.1.contDiffAt (V.isOpen.mem_nhds hyV) |>.continuousAt
        filter_upwards [Ω.isOpen.mem_nhds hy.1, hgc.preimage_mem_nhds (Ioi_mem_nhds hgy)] with z hz hgz
        exact ⟨hz, Or.inr hgz⟩
  have hdisj : Disjoint A B := disjoint_left.mpr (fun y hyA hyB => by
    rcases hyB.2 with h | h
    · exact hyA.2.1 h
    · exact h.ne' hyA.2.2)
  have hcover : connectedComponentIn (Ω : Set _) x ⊆ A ∪ B := by
    intro y hy
    have hyΩ := connectedComponentIn_subset (Ω : Set _) x hy
    by_cases hyx : y = x
    · exact Or.inr ⟨hyΩ, Or.inl hyx⟩
    · rcases (hnonneg y ⟨subset_closure hyΩ, by simpa using hyx⟩).eq_or_lt with h | h
      · exact Or.inl ⟨hyΩ, hyx, h.symm⟩
      · exact Or.inr ⟨hyΩ, Or.inr h⟩
  have hsub : connectedComponentIn (Ω : Set _) x ⊆ B :=
    isPreconnected_connectedComponentIn.subset_right_of_subset_union hA hB hdisj hcover
      ⟨x, mem_connectedComponentIn hx, hx, Or.inl rfl⟩
  intro y hy hxy
  exact (hsub hy).2.resolve_left (Ne.symm hxy)

/-- The real harmonic ball inequality is valid also in dimension one. -/
theorem harmonic_ball_submean {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u : Space n → ℝ) (hu : MeanValues.IsHarmonic Ω u) :
    P201Specs.SubharmonicMaximum.HasBallSubmean Ω (fun y => (u y : EReal)) := by
  have hmean := P201.SubharmonicMaximum.real_sphere_implies_ball hn Ω u hu.1.continuousOn
    (P201.SubharmonicMaximum.real_sphere_submean_of_laplacian_nonneg hn Ω u hu.1
      (fun y hy => (hu.2 y hy).ge))
  intro a r hr hball
  have hi : IntegrableOn u (ball a r) :=
    (hu.1.continuousOn.mono hball).integrableOn_compact (isCompact_closedBall a r)
      |>.mono_set ball_subset_closedBall
  rw [P201.SubharmonicMaximum.real_average_bridge _ _ hi,
    measureReal_restrict_apply_univ]
  exact EReal.coe_le_coe_iff.mpr (hmean a r hr hball)

/-- Continuous zero boundary values force a real harmonic function to be
nonpositive on a bounded open set in every positive dimension. A positive
maximum would have a nonempty compact maximum set which is also open. -/
theorem harmonic_boundary_nonpos {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hbounded : Bornology.IsBounded (Ω : Set (Space n))) (u : Space n → ℝ)
    (hu : MeanValues.IsHarmonic Ω u) (hc : ContinuousOn u (closure (Ω : Set _)))
    (hb : ∀ z ∈ frontier (Ω : Set _), u z ≤ 0) :
    ∀ y ∈ closure (Ω : Set _), u y ≤ 0 := by
  classical
  intro y hy
  by_contra hle
  have hpos : 0 < u y := lt_of_not_ge hle
  obtain ⟨a, ha, hmax⟩ := hbounded.isCompact_closure.exists_isMaxOn ⟨y, hy⟩ hc
  have hapos : 0 < u a := hpos.trans_le (hmax hy)
  let K := closure (Ω : Set _) ∩ u ⁻¹' {u a}
  have hK : IsCompact K := by
    have he : K = closure (Ω : Set _) ∩ u ⁻¹' Ici (u a) := by
      ext z
      exact ⟨fun hz => ⟨hz.1, (show u z = u a from hz.2).ge⟩,
        fun hz => ⟨hz.1, le_antisymm (hmax hz.1) hz.2⟩⟩
    rw [he]
    exact hc.upperSemicontinuousOn.isCompact_inter_preimage_Ici
      hbounded.isCompact_closure _
  have hKΩ : K ⊆ (Ω : Set _) := by
    intro z hz
    by_contra hzΩ
    have hzfr : z ∈ frontier (Ω : Set _) := by
      rw [Ω.isOpen.frontier_eq]; exact ⟨hz.1, hzΩ⟩
    have he : u z = u a := hz.2
    exact (hapos.trans_le (he ▸ hb z hzfr)).false
  have hKopen : IsOpen K := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds (hKΩ hz))
    have hclosed : closedBall z (r / 2) ⊆ (Ω : Set _) :=
      (closedBall_subset_ball (by linarith)).trans hball
    have hconst := P201.SubharmonicMaximum.ball_constant_of_max Ω
      (fun w => (u w : EReal))
      (continuous_coe_real_ereal.comp_continuousOn hu.1.continuousOn).upperSemicontinuousOn
      (harmonic_ball_submean hn Ω u hu) z (r / 2) (by linarith) hclosed (u a)
      (congrArg (fun t : ℝ => (t : EReal)) (show u z = u a from hz.2))
      (fun w hw => EReal.coe_le_coe_iff.mpr
        (hmax (subset_closure (hclosed (ball_subset_closedBall hw)))))
    apply Filter.mem_of_superset (ball_mem_nhds z (show 0 < r / 2 by linarith))
    intro w hw
    exact ⟨subset_closure (hclosed (ball_subset_closedBall hw)),
      EReal.coe_eq_coe_iff.mp (hconst w hw)⟩
  have hKuniv := (show IsClopen K from ⟨hK.isClosed, hKopen⟩).eq_univ ⟨a, ha, rfl⟩
  have : NeZero n := ⟨by omega⟩
  apply NormedSpace.unbounded_univ ℝ (Space n)
  rw [← hKuniv]
  exact hbounded.subset hKΩ

/-- A component of an open Euclidean set is closed relative to that set.
This formulation also controls whether its closure can meet another pole. -/
theorem closure_component_inter_domain {n : ℕ} (Ω : Domain n) (a : Space n) :
    closure (connectedComponentIn (Ω : Set _) a) ∩ (Ω : Set _) ⊆
      connectedComponentIn (Ω : Set _) a := by
  intro z hz
  have hnb : connectedComponentIn (Ω : Set _) z ∈ 𝓝 z :=
    Ω.isOpen.connectedComponentIn.mem_nhds (mem_connectedComponentIn hz.2)
  obtain ⟨w, hwz, hwa⟩ := mem_closure_iff_nhds.mp hz.1 _ hnb
  have he : connectedComponentIn (Ω : Set _) z = connectedComponentIn (Ω : Set _) a :=
    (connectedComponentIn_eq hwz).trans (connectedComponentIn_eq hwa).symm
  exact he ▸ mem_connectedComponentIn hz.2

/-- Each component's boundary lies on the original boundary, even when the
original domain has arbitrarily many components. -/
theorem frontier_component_subset {n : ℕ} (Ω : Domain n) (a : Space n) :
    frontier (connectedComponentIn (Ω : Set _) a) ⊆ frontier (Ω : Set _) := by
  intro z hz
  rw [Ω.isOpen.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset (Ω : Set (Space n)) a) hz.1, ?_⟩
  intro hzΩ
  apply hz.2
  rw [Ω.isOpen.connectedComponentIn.interior_eq]
  exact closure_component_inter_domain Ω a ⟨hz.1, hzΩ⟩

/-- On every other component, a Green row is harmonic through the entire
closure and has zero boundary data, hence vanishes. No correction hypothesis
or regularity of the component boundary is needed for this assertion. -/
theorem green_zero_other_component {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hbounded : Bornology.IsBounded (Ω : Set (Space n)))
    {x : Space n} (hx : x ∈ Ω) (g : Space n → ℝ) (hg : IsGreenFunction Ω x g)
    {y : Space n} (hy : y ∈ Ω) (hother : y ∉ connectedComponentIn (Ω : Set _) x) :
    g y = 0 := by
  let C : Domain n := ⟨connectedComponentIn (Ω : Set _) y, Ω.isOpen.connectedComponentIn⟩
  have hCΩ : (C : Set (Space n)) ⊆ (Ω : Set (Space n)) := by
    intro z hz
    exact connectedComponentIn_subset (Ω : Set (Space n)) y hz
  have hxC : x ∉ C := by
    intro h
    apply hother
    rw [← connectedComponentIn_eq h]
    exact mem_connectedComponentIn hy
  have hcl : closure (C : Set _) ⊆ closure (Ω : Set _) \ {x} := by
    intro z hz
    refine ⟨closure_mono hCΩ hz, ?_⟩
    simp only [mem_singleton_iff]
    intro hzx
    subst z
    exact hxC (closure_component_inter_domain Ω y ⟨hz, hx⟩)
  have hCV : C ≤ punctured Ω x := by
    intro z hz
    refine ⟨hCΩ hz, ?_⟩
    simp only [mem_singleton_iff]
    intro hzx
    exact hxC (hzx ▸ hz)
  have hgh : MeanValues.IsHarmonic C g :=
    ⟨hg.2.2.2.1.1.mono hCV, fun z hz => hg.2.2.2.1.2 z (hCV hz)⟩
  have hgc : ContinuousOn g (closure (C : Set _)) := hg.2.2.2.2.1.mono hcl
  have hgb : ∀ z ∈ frontier (C : Set _), g z = 0 := fun z hz =>
    hg.2.2.2.2.2 z (frontier_component_subset Ω y hz)
  have hpos := harmonic_boundary_nonpos hn C (hbounded.subset hCΩ) g hgh hgc
    (fun z hz => (hgb z hz).le) y (subset_closure (mem_connectedComponentIn hy))
  have hnegH : MeanValues.IsHarmonic C (fun z => -g z) :=
    (P201.MeanValues.harmonic_bridge C _).mpr
      (((P201.MeanValues.harmonic_bridge C g).mp hgh).neg)
  have hneg := harmonic_boundary_nonpos hn C (hbounded.subset hCΩ) (fun z => -g z)
    hnegH hgc.neg (fun z hz => by rw [hgb z hz]; simp) y
    (subset_closure (mem_connectedComponentIn hy))
  exact le_antisymm hpos (neg_nonpos.mp hneg)

/-- Conditional existence of each Green row in dimension at least two,
including the exact distributional normalization and the harmonic H²
correction. The other properties are established below and assembled in
`construction_conditional`. -/
theorem green_row_conditional
    (harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (hm : 1 ≤ m) (Ω : Domain (m + 1))
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasCkBoundary Ω 2) {x : Space (m + 1)} (hx : x ∈ Ω) :
    ∃ g : Space (m + 1) → ℝ, IsGreenFunction Ω x g ∧ HasHarmonicCorrection Ω x g := by
  obtain ⟨h, hh, hc, hb, hw⟩ :=
    harmonic_correction_conditional harmonic_lift hm Ω hbounded hboundary hx
  let f := fun y => fundamentalKernel (m + 1) (y - x)
  let g := fun y => f y - h y
  have hn : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have hfl : LocallyIntegrableOn f Ω volume :=
    (translated_fundamental_locallyIntegrable hn x).locallyIntegrableOn _
  have hhl : LocallyIntegrableOn h Ω volume :=
    hh.1.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hfcd : ContDiffOn ℝ (⊤ : ℕ∞) f (punctured Ω x) := fun y hy =>
    (translated_fundamental_contDiffAt x (by simpa using hy.2)).contDiffWithinAt
  have hhcd : ContDiffOn ℝ (⊤ : ℕ∞) h Ω :=
    P201.MeanValues.sphere_mean_implies_contDiffOn hn Ω h hh.1.continuousOn
      (P201.MeanValues.harmonic_sphere_means hn Ω h hh)
  refine ⟨g, ⟨hfl.sub hhl, ?_, hfcd.sub (hhcd.mono (fun _ hy => hy.1)), ?_, ?_, ?_⟩,
    h, hh, hc, hb, hw, fun _ _ => rfl⟩
  · have hnorm : -distributionLaplacian
        (regularDistribution Ω f - regularDistribution Ω h) = poleDirac Ω x := by
      rw [distributionLaplacian_sub, harmonic_distribution_zero Ω h hh, sub_zero]
      exact translated_fundamental_solution hn Ω x
    exact (congrArg (fun U : Distribution ℝ Ω => -distributionLaplacian U)
      (regular_sub Ω f h hfl hhl)).trans hnorm
  · exact harmonic_sub (punctured Ω x) f h (translated_fundamental_harmonic hn Ω x)
      ⟨hh.1.mono (fun _ hy => hy.1), fun y hy => hh.2 y hy.1⟩
  · have hfc : ContinuousOn f (closure (Ω : Set _) \ {x}) := fun y hy =>
      (translated_fundamental_contDiffAt x (by simpa using hy.2)).continuousAt.continuousWithinAt
    exact hfc.sub (hc.mono sdiff_subset)
  · intro z hz
    exact sub_eq_zero.mpr (hb z hz).symm

/-- Uniqueness across the pole follows from the distribution equation, Weyl's
lemma and the maximum principle in every positive dimension. The proof fills in the pole using
the Weyl representative before applying boundary uniqueness. -/
theorem green_unique {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hbounded : Bornology.IsBounded (Ω : Set (Space n)))
    {x : Space n} (hx : x ∈ Ω) (g : Space n → ℝ) (hg : IsGreenFunction Ω x g) :
    UniqueGreenFunction Ω x g := by
  classical
  intro v hv
  obtain ⟨hgl, hgΔ, _, _, hgc, hgb⟩ := hg
  obtain ⟨hvl, hvΔ, _, _, hvc, hvb⟩ := hv
  let f := fun y => v y - g y
  have hfl : LocallyIntegrableOn f Ω volume := hvl.sub hgl
  have hΔ : distributionLaplacian (regularDistribution Ω f) = 0 := by
    have he : distributionLaplacian (regularDistribution Ω v) =
        distributionLaplacian (regularDistribution Ω g) := neg_injective (hvΔ.trans hgΔ.symm)
    have hl := congrArg (fun U : Distribution ℝ Ω => distributionLaplacian U)
      (regular_sub Ω v g hvl hgl)
    exact hl.trans (by rw [distributionLaplacian_sub, he, sub_self])
  obtain ⟨u, hucd, huh, hurep, _⟩ := P201.Weyl.weyl hn Ω
    (regularDistribution Ω f) hΔ
  let V := punctured Ω x
  have hV : V ≤ Ω := fun _ hy => hy.1
  have hfc : ContinuousOn f (closure (Ω : Set _) \ {x}) := hvc.sub hgc
  have heu : EqOn u f V := by
    apply P201.Weyl.continuous_representative_unique V u f
      (hucd.continuousOn.mono hV) (hfc.mono (fun y hy => ⟨subset_closure hy.1, hy.2⟩))
    calc
      regularDistribution V u = P102.U4.restrictDistribution hV (regularDistribution Ω u) :=
        (P201.Weyl.regular_restriction hV u
          (hucd.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)).symm
      _ = P102.U4.restrictDistribution hV (regularDistribution Ω f) := congrArg _ hurep
      _ = regularDistribution V f := P201.Weyl.regular_restriction hV f hfl
  let F := fun y => if y ∈ Ω then u y else f y
  have hFgerm (y : Space n) (hy : y ∈ Ω) : F =ᶠ[𝓝 y] u := by
    filter_upwards [Ω.isOpen.mem_nhds hy] with z hz
    exact ite_eq_left hz
  have hFeq : EqOn F f (closure (Ω : Set _) \ {x}) := by
    intro y hy
    by_cases hyΩ : y ∈ Ω
    · exact (ite_eq_left hyΩ).trans (heu ⟨hyΩ, hy.2⟩)
    · exact ite_eq_right hyΩ
  have hFcAway : ContinuousOn F (closure (Ω : Set _) \ {x}) :=
    hfc.congr hFeq
  have hFc : ContinuousOn F (closure (Ω : Set _)) := by
    intro y hy
    by_cases hyΩ : y ∈ Ω
    · exact ((hucd.contDiffAt (Ω.isOpen.mem_nhds hyΩ)).continuousAt.congr_of_eventuallyEq
        (hFgerm y hyΩ)).continuousWithinAt
    · apply continuousWithinAt_sdiff_singleton.mp
      exact hFcAway y ⟨hy, by simpa using (show y ≠ x from fun he => hyΩ (he.symm ▸ hx))⟩
  have hFh : MeanValues.IsHarmonic Ω F := by
    refine ⟨fun y hy => ((hucd.contDiffAt (Ω.isOpen.mem_nhds hy)).of_le (by simp)
      |>.congr_of_eventuallyEq (hFgerm y hy)).contDiffWithinAt, fun y hy => ?_⟩
    exact (P201.Weyl.laplacian_eq_of_eventuallyEq (hFgerm y hy)).trans (huh.2 y hy)
  have hFb : ∀ z ∈ frontier (Ω : Set _), F z = 0 := by
    intro z hz
    have hzΩ : z ∉ Ω :=
      Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr Ω.isOpen) hz
    simp [F, hzΩ, f, hvb z hz, hgb z hz]
  have hFzero : EqOn F (fun _ => (0 : ℝ)) (closure (Ω : Set _)) := by
    have hpos := harmonic_boundary_nonpos hn Ω hbounded F hFh hFc
      (fun z hz => (hFb z hz).le)
    have hnegH : MeanValues.IsHarmonic Ω (fun z => -F z) :=
      (P201.MeanValues.harmonic_bridge Ω _).mpr
        (((P201.MeanValues.harmonic_bridge Ω F).mp hFh).neg)
    have hneg := harmonic_boundary_nonpos hn Ω hbounded (fun z => -F z) hnegH hFc.neg
      (fun z hz => by rw [hFb z hz]; simp)
    exact fun z hz => le_antisymm (hpos z hz) (neg_nonpos.mp (hneg z hz))
  have hUz : regularDistribution Ω u = 0 := by
    have hreg : regularDistribution Ω u = regularDistribution Ω (fun _ => (0 : ℝ)) := by
      apply (P102.U4.regular_injectivity n ℝ Ω _ _
        (hucd.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
        locallyIntegrableOn_zero).mpr
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
      exact (ite_eq_left hy).symm.trans (hFzero (subset_closure hy))
    exact hreg.trans (regular_zero Ω)
  refine ⟨sub_eq_zero.mp ((regular_sub Ω v g hvl hgl).symm.trans (hurep.symm.trans hUz)), ?_⟩
  intro y hy
  exact sub_eq_zero.mp ((hFeq hy).symm.trans (hFzero hy.1))

/-- The higher-dimensional conditional interface is retained for the
construction helpers; uniqueness itself needs no smooth-lifting premise. -/
theorem green_unique_conditional
    (_harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (_hm : 1 ≤ m) (Ω : Domain (m + 1))
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (_hboundary : HasCkBoundary Ω 2) {x : Space (m + 1)} (hx : x ∈ Ω)
    (g : Space (m + 1) → ℝ) (hg : IsGreenFunction Ω x g) :
    UniqueGreenFunction Ω x g :=
  green_unique (by omega) Ω hbounded hx g hg

/-- Assembly of the proved higher-dimensional existence and uniqueness
portion into one kernel, retaining its pointwise harmonic-correction formula.
The sign, symmetry, trace and one-dimensional clauses are handled by later
lemmas; this helper only assembles the rows. -/
theorem green_kernel_conditional
    (harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (hm : 1 ≤ m) (Ω : Domain (m + 1))
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasCkBoundary Ω 2) :
    ∃ G : Space (m + 1) → Space (m + 1) → ℝ,
      ∀ x ∈ Ω, IsGreenFunction Ω x (G x) ∧ UniqueGreenFunction Ω x (G x) ∧
        HasHarmonicCorrection Ω x (G x) := by
  classical
  have hrow (x : Ω) := green_row_conditional harmonic_lift hm Ω hbounded hboundary x.property
  choose g hg using hrow
  let G := fun x => if hx : x ∈ Ω then g ⟨x, hx⟩ else (fun _ => 0)
  refine ⟨G, fun x hx => ?_⟩
  have he : G x = g ⟨x, hx⟩ := dite_eq_left hx
  rw [he]
  exact ⟨(hg ⟨x, hx⟩).1,
    green_unique_conditional harmonic_lift hm Ω hbounded hboundary hx _ (hg ⟨x, hx⟩).1,
    (hg ⟨x, hx⟩).2⟩

/-- Higher-dimensional construction with all componentwise sign assertions.
Symmetry and boundary-collar regularity are supplied by later lemmas. -/
theorem green_kernel_signs_conditional
    (harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (hm : 1 ≤ m) (Ω : Domain (m + 1))
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasCkBoundary Ω 2) :
    ∃ G : Space (m + 1) → Space (m + 1) → ℝ,
      (∀ x ∈ Ω, IsGreenFunction Ω x (G x) ∧ UniqueGreenFunction Ω x (G x) ∧
        HasHarmonicCorrection Ω x (G x)) ∧
      (∀ x ∈ Ω, ∀ y ∈ closure (Ω : Set _) \ {x}, 0 ≤ G x y) ∧
      (∀ x ∈ Ω, ∀ y ∈ connectedComponentIn (Ω : Set _) x, x ≠ y → 0 < G x y) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, y ∉ connectedComponentIn (Ω : Set _) x → G x y = 0) := by
  obtain ⟨G, hG⟩ := green_kernel_conditional harmonic_lift hm Ω hbounded hboundary
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro x hx
    exact green_nonnegative (by omega) Ω hbounded hx (G x) (hG x hx).1 (hG x hx).2.2
  · intro x hx
    exact green_positive (by omega) Ω hbounded hx (G x) (hG x hx).1 (hG x hx).2.2
  · intro x hx y hy hother
    exact green_zero_other_component (by omega) Ω hbounded hx (G x) (hG x hx).1 hy hother

/-- Every globally smooth function has its actual Sobolev class on a bounded open set. -/
theorem bounded_smooth_hilbert_realization {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (k : ℕ)
    (f : Space n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∃ u : H ℝ Ω k, (hUnderlying Ω k u : Space n → ℝ) =ᵐ[domainMeasure Ω] f := by
  obtain ⟨R, hR, hΩR⟩ := hb.subset_ball_lt 0 (0 : Space n)
  let β : ContDiffBump (0 : Space n) := ⟨R, R + 1, hR, by linarith⟩
  let φ : P102.U4.WholeTests n ℝ :=
    ⟨fun z => β z * f z, β.contDiff.mul hf, β.hasCompactSupport.mul_right, subset_univ _⟩
  obtain ⟨w, hw⟩ := P102.U4.wholeSpace_smoothTests k 2 φ
  let v := P102.U4.sobolevRestrict Ω w
  refine ⟨(hToW ℝ Ω k).symm v, ?_⟩
  have hw0 := hw (P102.U4.zeroSobolevIndex n k)
  simp only [P102.U4.zeroSobolevIndex, P102.U4.multiPartial, Multiset.sort_zero,
    P102.U4.partialWord] at hw0
  have hv0 : (hUnderlying Ω k ((hToW ℝ Ω k).symm v) : Space n → ℝ)
      =ᵐ[domainMeasure Ω] φ :=
    (P102.U4.domainLpRestrict_ae Ω _).trans (ae_restrict_of_ae hw0)
  filter_upwards [hv0, ae_restrict_mem Ω.isOpen.measurableSet] with y hy hyΩ
  rw [hy]
  change β y * f y = f y
  rw [β.one_of_mem_closedBall (ball_subset_closedBall (hΩR hyΩ)), one_mul]

/-- Restrict the complete Hilbert Sobolev derivative graph to any smaller open. -/
def hilbertRestrict {n : ℕ} {U V : Domain n} (h : V ≤ U) (k : ℕ) :
    H ℝ U k →L[ℝ] H ℝ V k :=
  ((hToW ℝ V k).symm.toContinuousLinearMap.comp
    (P102.Sobolev.Extension.sobolevRestrict h k 2)).comp
    (hToW ℝ U k).toContinuousLinearMap

lemma hilbertRestrict_ae {n : ℕ} {U V : Domain n} (h : V ≤ U) (k : ℕ)
    (u : H ℝ U k) :
    (hUnderlying V k (hilbertRestrict h k u) : Space n → ℝ) =ᵐ[domainMeasure V]
      hUnderlying U k u := by
  exact P102.Sobolev.Extension.sobolevRestrict_derivative_ae h k 2
    ((hToW ℝ U k) u) (P102.U4.zeroSobolevIndex n k)

/-- The pole singularity can be removed smoothly while retaining the fundamental
solution outside any prescribed positive ball. -/
theorem smooth_fundamental_exterior {n : ℕ} (x : Space n) {r : ℝ} (hr : 0 < r) :
    ∃ F : Space n → ℝ, ContDiff ℝ ∞ F ∧
      ∀ y, r ≤ dist y x → F y = fundamentalKernel n (y - x) := by
  let β : ContDiffBump x := ⟨r / 2, r, by positivity, by linarith⟩
  let F := fun z => (1 - β z) * fundamentalKernel n (z - x)
  refine ⟨F, contDiff_iff_contDiffAt.mpr (fun z => ?_), ?_⟩
  · by_cases hz : z = x
    · subst z
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [β.eventuallyEq_one] with z hz
      simp [F, hz]
    · exact (contDiffAt_const.sub β.contDiffAt).mul
        (translated_fundamental_contDiffAt x hz)
  · intro y hy
    simp [F, β.zero_of_le_dist hy]

/-- Every interior pole admits a positive collar radius with twice the radius
still contained in the original open set. -/
theorem exists_collar_radius {n : ℕ} (Ω : Domain n) {x : Space n} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ closedBall x (2 * r) ⊆ (Ω : Set (Space n)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  refine ⟨ε / 4, by positivity, ?_⟩
  exact (closedBall_subset_ball (by linarith)).trans hball

/-- Removing the pole ball introduces only its sphere as a possible new
boundary. This statement is independent of boundary regularity. -/
theorem frontier_collar_subset {n : ℕ} (Ω : Domain n) (x : Space n) (r : ℝ) :
    frontier (collar Ω x r : Set (Space n)) ⊆
      frontier (Ω : Set (Space n)) ∪ sphere x r := by
  intro z hz
  have h := frontier_inter_subset (Ω : Set (Space n)) (closedBall x r)ᶜ hz
  rcases h with h | h
  · exact Or.inl h.1
  · have hfr : z ∈ frontier (closedBall x r) := by
      simpa only [frontier_compl] using h.2
    exact Or.inr (frontier_closedBall_subset_sphere hfr)

/-- The two possible collar boundaries are separated by the interior ball.
Near the outer boundary the collar and the original domain coincide. -/
theorem collar_outer_boundary_germ {n : ℕ} (Ω : Domain n) {x z : Space n}
    {r : ℝ} (hr : 0 < r) (hball : closedBall x (2 * r) ⊆ (Ω : Set (Space n)))
    (hz : z ∈ frontier (Ω : Set (Space n))) :
    2 * r < dist z x ∧
      ∀ᶠ y in 𝓝 z, (y ∈ collar Ω x r ↔ y ∈ Ω) := by
  have hzΩ : z ∉ Ω := (Ω.isOpen.frontier_eq ▸ hz).2
  have hd : 2 * r < dist z x := lt_of_not_ge fun h => hzΩ (hball h)
  refine ⟨hd, ?_⟩
  have hzout : z ∉ closedBall x r := fun h => (by linarith : r < dist z x).not_ge h
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hzout] with y hy
  exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

/-- Near the inner sphere the collar is exactly the exterior of its ball;
the original domain contributes no further boundary there. -/
theorem collar_inner_boundary_germ {n : ℕ} (Ω : Domain n) {x z : Space n}
    {r : ℝ} (hr : 0 < r) (hball : closedBall x (2 * r) ⊆ (Ω : Set (Space n)))
    (hz : z ∈ sphere x r) :
    z ∈ Ω ∧ ∀ᶠ y in 𝓝 z, (y ∈ collar Ω x r ↔ r < dist y x) := by
  have hzΩ : z ∈ Ω := hball (by
    change dist z x ≤ 2 * r
    rw [mem_sphere.mp hz]
    linarith)
  refine ⟨hzΩ, ?_⟩
  filter_upwards [Ω.isOpen.mem_nhds hzΩ] with y hy
  exact ⟨fun h => lt_of_not_ge h.2, fun h => ⟨hy, not_le_of_gt h⟩⟩

/-- The harmonic correction supplies the actual H² class on each exterior
collar. This needs no regularity assertion about the collar boundary. -/
theorem green_collar_h2 {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) {x : Space n}
    (g : Space n → ℝ) (hcorr : HasHarmonicCorrection Ω x g)
    {r : ℝ} (hr : 0 < r) :
    ∃ w : H ℝ (collar Ω x r) 2,
      (hUnderlying (collar Ω x r) 2 w : Space n → ℝ)
        =ᵐ[domainMeasure (collar Ω x r)] g := by
  obtain ⟨h, _, _, _, ⟨w, hw⟩, hformula⟩ := hcorr
  let C := collar Ω x r
  have hCΩ : C ≤ Ω := fun _ hy => hy.1
  obtain ⟨F, hF, hFeq⟩ := smooth_fundamental_exterior x hr
  obtain ⟨v, hv⟩ := bounded_smooth_hilbert_realization C
    (hb.subset (fun _ hy => hy.1)) 2 F hF
  let wC := hilbertRestrict hCΩ 2 w
  refine ⟨v - wC, ?_⟩
  have hwC : (hUnderlying C 2 wC : Space n → ℝ) =ᵐ[domainMeasure C] h :=
    (hilbertRestrict_ae hCΩ 2 w).trans (ae_mono (Measure.restrict_mono hCΩ le_rfl) hw)
  have hsub := Lp.coeFn_sub (hUnderlying C 2 v) (hUnderlying C 2 wC)
  rw [map_sub]
  filter_upwards [hsub, hv, hwC, ae_restrict_mem C.isOpen.measurableSet]
    with y hys hyv hyw hyC
  rw [hys]
  change hUnderlying C 2 v y - hUnderlying C 2 wC y = g y
  rw [hyv, hyw]
  have hyrc : r < dist y x := lt_of_not_ge hyC.2
  have hyx : y ≠ x := by
    intro h
    subst y
    have : r < 0 := by simpa using hyrc
    linarith
  rw [hFeq y hyrc.le]
  exact (hformula y ⟨subset_closure hyC.1, by simpa using hyx⟩).symm


/-- Every H² class determines the same function as an H¹ class, with H¹
classes for every first weak derivative. This uses the complete weak graphs. -/
theorem h2_h1_gradient_classes {n : ℕ} (U : Domain n) (w : H ℝ U 2) :
    ∃ (u : H ℝ U 1) (v : Fin n → H ℝ U 1),
      hUnderlying U 1 u = hUnderlying U 2 w ∧
      ∀ i, hUnderlying U 1 (v i) = hFirstDerivative u i := by
  have hmem : P102.U4.HasSobolevDerivatives U 1 2 (hUnderlying U 2 w) := by
    intro α hα
    exact ⟨w.val ⟨α, hα.trans (by norm_num)⟩,
      P201.hilbertDerivativeDistribution U 2 w ⟨α, hα.trans (by norm_num)⟩⟩
  obtain ⟨uW, huW⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range U 1 2)
    (hUnderlying U 2 w)).mpr hmem
  let u := (hToW ℝ U 1).symm uW
  have hu : hUnderlying U 1 u = hUnderlying U 2 w := huW
  have hfirst (i : Fin n) : hFirstDerivative u i = w.val ⟨{i}, by simp⟩ := by
    apply P102.U4.regularLp_injective U 2
    have hi := P201.hilbertDerivativeDistribution U 1 u ⟨{i}, by simp⟩
    change distributionDerivative {i} (regularDistribution U (hUnderlying U 1 u)) =
      regularDistribution U (hFirstDerivative u i) at hi
    rw [hu] at hi
    exact hi.symm.trans (P201.hilbertDerivativeDistribution U 2 w ⟨{i}, by simp⟩)
  have hv (i : Fin n) : ∃ v : H ℝ U 1,
      hUnderlying U 1 v = hFirstDerivative u i := by
    have hmemi : P102.U4.HasSobolevDerivatives U 1 2 (hFirstDerivative u i) := by
      intro α hα
      have hbound : (α + {i} : MultiIndex n).card ≤ 2 := by simp; omega
      refine ⟨w.val ⟨α + {i}, hbound⟩, ?_⟩
      rw [hfirst i]
      have hi := P201.hilbertDerivativeDistribution U 2 w ⟨{i}, by simp⟩
      change distributionDerivative {i} (regularDistribution U (hUnderlying U 2 w)) =
        regularDistribution U (w.val ⟨{i}, by simp⟩) at hi
      calc
        _ = distributionDerivative α (distributionDerivative {i}
            (regularDistribution U (hUnderlying U 2 w))) :=
          congrArg (distributionDerivative α) hi.symm
        _ = distributionDerivative (α + {i}) (regularDistribution U (hUnderlying U 2 w)) :=
          (P102.U4.derivative_add n ℝ U α {i} _).symm
        _ = _ := P201.hilbertDerivativeDistribution U 2 w ⟨α + {i}, hbound⟩
    obtain ⟨vW, hvW⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range U 1 2)
      (hFirstDerivative u i)).mpr hmemi
    exact ⟨(hToW ℝ U 1).symm vW, hvW⟩
  choose v hv using hv
  exact ⟨u, v, hu, hv⟩

/-- Restricting a Green row to a positive exterior collar gives the genuine
H¹ harmonic class and genuine H¹ classes for its gradient components. -/
theorem green_collar_harmonic_classes {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) {x : Space n}
    (g : Space n → ℝ) (hg : IsGreenFunction Ω x g)
    (hcorr : HasHarmonicCorrection Ω x g) {r : ℝ} (hr : 0 < r) :
    ∃ (u : H ℝ (collar Ω x r) 1) (w : H ℝ (collar Ω x r) 2)
      (v : Fin n → H ℝ (collar Ω x r) 1),
      (hUnderlying (collar Ω x r) 1 u : Space n → ℝ)
        =ᵐ[domainMeasure (collar Ω x r)] g ∧
      (hUnderlying (collar Ω x r) 2 w : Space n → ℝ)
        =ᵐ[domainMeasure (collar Ω x r)] g ∧
      P201Specs.NormalTrace.HasLaplacian (collar Ω x r) u 0 ∧
      ∀ i, (hUnderlying (collar Ω x r) 1 (v i) : Space n → ℝ)
        =ᵐ[domainMeasure (collar Ω x r)] fun y => hGradient u y i := by
  let C := collar Ω x r
  obtain ⟨w, hw⟩ := green_collar_h2 Ω hb g hcorr hr
  obtain ⟨u, v, hu, hv⟩ := h2_h1_gradient_classes C w
  have hug : (hUnderlying C 1 u : Space n → ℝ) =ᵐ[domainMeasure C] g := by
    rw [hu]
    exact hw
  refine ⟨u, w, v, hug, hw, ?_, ?_⟩
  · have hCV : C ≤ punctured Ω x := by
      intro y hy
      refine ⟨hy.1, ?_⟩
      simp only [mem_singleton_iff]
      intro heq
      subst y
      exact hy.2 (mem_closedBall_self hr.le)
    have hgh : P201Specs.MeanValues.IsHarmonic C g :=
      ⟨hg.2.2.2.1.1.mono hCV, fun y hy => hg.2.2.2.1.2 y (hCV hy)⟩
    have he : regularDistribution C (hUnderlying C 1 u) = regularDistribution C g :=
      (P102.U4.regular_injectivity n ℝ C _ _
        (P102.U4.domainLp_locallyIntegrable C 2 _)
        (hgh.1.continuousOn.locallyIntegrableOn C.isOpen.measurableSet)).mpr hug
    change distributionLaplacian (regularDistribution C (hUnderlying C 1 u)) = _
    rw [he, harmonic_distribution_zero C g hgh]
    ext φ
    rw [P102.U4.regular_pairing n ℝ C _ (P102.U4.domainLp_locallyIntegrable C 2 0)]
    have hzero := Lp.coeFn_zero ℝ 2 (domainMeasure C)
    change 0 = ∫ y in C, (0 : Lp ℝ C 2) y * φ y
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with y hy
    have hy0 : (0 : Lp ℝ C 2) y = 0 := hy
    rw [hy0, zero_mul]
    rfl
  · intro i
    have hga : (hGradient u : Space n → Space n) =ᵐ[domainMeasure C]
        fun y => WithLp.toLp 2 (fun j => hFirstDerivative u j y) := MemLp.coeFn_toLp _
    rw [hv i]
    filter_upwards [hga] with y hy
    exact (congrArg (fun z : Space n => z i) hy).symm

open P102.Trace.Ordinary
theorem one_component_interval (Ω : Domain 1)
    (hbounded : Bornology.IsBounded (Ω : Set (Space 1)))
    {x : Space 1} (hx : x ∈ Ω) :
    ∃ a b : ℝ, a < x 0 ∧ x 0 < b ∧
      connectedComponentIn (Ω : Set _) x = linePoint '' Ioo a b := by
  let e := lineIsometry
  let C := connectedComponentIn (Ω : Set _) x
  let D := e.symm '' C
  have hCo : IsOpen C := Ω.isOpen.connectedComponentIn
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  have hCb : Bornology.IsBounded C :=
    hbounded.subset (connectedComponentIn_subset (Ω : Set _) x)
  have hDo : IsOpen D := e.symm.toHomeomorph.isOpenMap _ hCo
  have hDc : IsConnected D := hCc.image _ e.symm.continuous.continuousOn
  have hDb : Bornology.IsBounded D := e.symm.lipschitzWith.isBounded_image hCb
  have hD : D = Ioo (sInf D) (sSup D) :=
    P102.Sobolev.Geometry.RealDecomposition.open_connected_eq_Ioo hDo hDc hDb
  have hxD : x 0 ∈ D := ⟨x, mem_connectedComponentIn hx, rfl⟩
  refine ⟨sInf D, sSup D, (hD ▸ hxD).1, (hD ▸ hxD).2, ?_⟩
  rw [← hD]
  change C = e '' (e.symm '' C)
  rw [image_image]
  simp

theorem affine_harmonicAt {n : ℕ} (L : Space n →L[ℝ] ℝ) (c : ℝ) (x : Space n) :
    InnerProductSpace.HarmonicAt (fun y => L y + c) x := by
  refine ⟨L.contDiff.contDiffAt.add contDiffAt_const, ?_⟩
  filter_upwards [] with y
  rw [← P201.MeanValues.laplacian_bridge (fun y => L y + c) y
    (L.contDiff.contDiffAt.add contDiffAt_const)]
  simp [P201Specs.laplacian, P201Specs.multiPartial, P102.U4.multiPartial,
    Multiset.sort_cons, P102.U4.partialWord, fderiv_add_const,
    L.fderiv]

/-- Clamping the ordinate gives a continuous tent with zero exterior values. -/
def intervalTent (a b x t : ℝ) : ℝ :=
  intervalKernel a b x (max a (min b t))

theorem intervalTent_continuous (a b x : ℝ) : Continuous (intervalTent a b x) := by
  apply (intervalKernel_continuous a b x).comp
  fun_prop

theorem intervalTent_eq {a b x t : ℝ} (ht : t ∈ Icc a b) :
    intervalTent a b x t = intervalKernel a b x t := by
  simp [intervalTent, min_eq_right ht.2, max_eq_right ht.1]

theorem intervalTent_zero {a b x t : ℝ} (hx : x ∈ Ioo a b) (ht : t ∉ Ioo a b) :
    intervalTent a b x t = 0 := by
  have ha := (intervalKernel_endpoints hx.1.le hx.2.le).1
  have hb := (intervalKernel_endpoints hx.1.le hx.2.le).2
  rcases le_or_gt t a with ht | ht
  · rw [intervalTent, max_eq_left ((min_le_right b t).trans ht), ha]
  · have hb' : b ≤ t := le_of_not_gt (fun h => by exact ‹t ∉ Ioo a b› ⟨ht, h⟩)
    rw [intervalTent, min_eq_left hb', max_eq_right (hx.1.trans hx.2).le, hb]

theorem fundamental_one_coordinate (x y : Space 1) :
    fundamentalKernel 1 (y - x) = -|y 0 - x 0| / 2 := by
  change -‖y - x‖ / 2 = _
  have hn : ‖y - x‖ = |y 0 - x 0| := by
    have h := lineIsometry.symm.norm_map (y - x)
    change ‖y 0 - x 0‖ = ‖y - x‖ at h
    simpa only [Real.norm_eq_abs] using h.symm
  rw [hn]

theorem interval_correction_affine {a b x t : ℝ} (hx : x ∈ Ioo a b) :
    -|t - x| / 2 - intervalKernel a b x t =
      ((2 * x - a - b) / (2 * (b - a))) * t +
        (-x / 2 + a * (b - x) / (b - a)) := by
  have hab : b - a ≠ 0 := ne_of_gt (sub_pos.mpr (hx.1.trans hx.2))
  rcases le_or_gt t x with h | h
  · rw [intervalKernel_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    field_simp
    ring
  · rw [intervalKernel_right h.le, abs_of_nonneg (sub_nonneg.mpr h.le)]
    field_simp
    ring

theorem intervalTent_correction_regular (Ω : Domain 1) {x : Space 1}
    (hx : x ∈ Ω) {a b : ℝ} (hxab : x 0 ∈ Ioo a b)
    (hC : connectedComponentIn (Ω : Set _) x = linePoint '' Ioo a b) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Space 1 => fundamentalKernel 1 (y - x) - intervalTent a b (x 0) (y 0)) Ω ∧
    MeanValues.IsHarmonic Ω
      (fun y : Space 1 => fundamentalKernel 1 (y - x) - intervalTent a b (x 0) (y 0)) := by
  let f := fun y : Space 1 => fundamentalKernel 1 (y - x) - intervalTent a b (x 0) (y 0)
  have hlocal : ∀ y ∈ Ω,
      ContDiffAt ℝ (⊤ : ℕ∞) f y ∧ InnerProductSpace.HarmonicAt f y := by
    intro y hy
    by_cases hyC : y ∈ connectedComponentIn (Ω : Set _) x
    · have hyab : y 0 ∈ Ioo a b := by
        rw [hC] at hyC
        obtain ⟨t, ht, rfl⟩ := hyC
        exact ht
      let L : Space 1 →L[ℝ] ℝ :=
        ((2 * x 0 - a - b) / (2 * (b - a))) • EuclideanSpace.proj 0
      let c : ℝ := -x 0 / 2 + a * (b - x 0) / (b - a)
      have hc : Continuous (fun z : Space 1 => z 0) := (EuclideanSpace.proj 0).continuous
      have he : f =ᶠ[𝓝 y] (fun z => L z + c) := by
        filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hyab)] with z hz
        change fundamentalKernel 1 (z - x) - intervalTent a b (x 0) (z 0) = _
        rw [fundamental_one_coordinate x z]
        rw [intervalTent_eq ⟨hz.1.le, hz.2.le⟩, interval_correction_affine hxab]
        rfl
      exact ⟨(L.contDiff.contDiffAt.add contDiffAt_const).congr_of_eventuallyEq he,
        (InnerProductSpace.harmonicAt_congr_nhds he).mpr (affine_harmonicAt L c y)⟩
    · have hyncl : y ∉ closure (connectedComponentIn (Ω : Set _) x) := fun h =>
        hyC (closure_component_inter_domain Ω x ⟨h, hy⟩)
      have hyx : y ≠ x := by
        intro h
        apply hyC
        rw [h]
        exact mem_connectedComponentIn hx
      have he : f =ᶠ[𝓝 y] (fun z => fundamentalKernel 1 (z - x)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hyncl] with z hz
        have hzC : z ∉ connectedComponentIn (Ω : Set _) x :=
          fun h => hz (subset_closure h)
        have hzab : z 0 ∉ Ioo a b := by
          intro hab
          apply hzC
          rw [hC]
          exact ⟨z 0, hab, lineIsometry.apply_symm_apply z⟩
        simp only [f, intervalTent_zero hxab hzab, sub_zero]
      have hfH := (P201.MeanValues.harmonic_bridge (punctured Ω x) _).mp
        (translated_fundamental_harmonic (by omega : 1 ≤ 1) Ω x) y ⟨hy, by simpa⟩
      exact ⟨(translated_fundamental_contDiffAt x hyx).congr_of_eventuallyEq he,
        (InnerProductSpace.harmonicAt_congr_nhds he).mpr hfH⟩
  exact ⟨fun y hy => (hlocal y hy).1.contDiffWithinAt,
    (P201.MeanValues.harmonic_bridge Ω f).mpr (fun y hy => (hlocal y hy).2)⟩

theorem intervalTent_green (Ω : Domain 1) {x : Space 1}
    (hx : x ∈ Ω) {a b : ℝ} (hxab : x 0 ∈ Ioo a b)
    (hC : connectedComponentIn (Ω : Set _) x = linePoint '' Ioo a b) :
    IsGreenFunction Ω x (fun y : Space 1 => intervalTent a b (x 0) (y 0)) ∧
      HasIntervalFormula Ω x (fun y : Space 1 => intervalTent a b (x 0) (y 0)) := by
  let f := fun y : Space 1 => fundamentalKernel 1 (y - x)
  let g := fun y : Space 1 => intervalTent a b (x 0) (y 0)
  let h := fun y => f y - g y
  have hgC : Continuous g := (intervalTent_continuous a b (x 0)).comp
    (EuclideanSpace.proj 0).continuous
  have hgl : LocallyIntegrableOn g Ω volume := hgC.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  obtain ⟨hhS, hhH⟩ := intervalTent_correction_regular Ω hx hxab hC
  have hhl : LocallyIntegrableOn h Ω volume :=
    hhH.1.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hfl := (translated_fundamental_locallyIntegrable (by omega : 1 ≤ 1) x).locallyIntegrableOn (Ω : Set _)
  have hge : g = (fun y => f y - h y) := by funext y; dsimp [h]; ring
  have hnorm : -distributionLaplacian (regularDistribution Ω g) = poleDirac Ω x := by
    rw [hge, regular_sub Ω f h hfl hhl, distributionLaplacian_sub,
      harmonic_distribution_zero Ω h hhH, sub_zero]
    exact translated_fundamental_solution (by omega : 1 ≤ 1) Ω x
  have hgS : ContDiffOn ℝ (⊤ : ℕ∞) g (punctured Ω x) := by
    rw [hge]
    have hfS : ContDiffOn ℝ (⊤ : ℕ∞) f (punctured Ω x) := fun y hy =>
      (translated_fundamental_contDiffAt x (by simpa using hy.2)).contDiffWithinAt
    exact hfS.sub (hhS.mono (by intro y hy; exact hy.1))
  have hgH : MeanValues.IsHarmonic (punctured Ω x) g := by
    rw [hge]
    exact harmonic_sub (punctured Ω x) f h
      (translated_fundamental_harmonic (by omega : 1 ≤ 1) Ω x)
      ⟨hhH.1.mono (by intro y hy; exact hy.1), fun y hy => hhH.2 y hy.1⟩
  have hzero : ∀ y : Space 1, y ∉ connectedComponentIn (Ω : Set _) x → g y = 0 := by
    intro y hy
    have hyab : y 0 ∉ Ioo a b := by
      intro hab
      apply hy
      rw [hC]
      exact ⟨y 0, hab, lineIsometry.apply_symm_apply y⟩
    exact intervalTent_zero hxab hyab
  refine ⟨⟨hgl, hnorm, hgS, hgH, hgC.continuousOn, ?_⟩,
    a, b, hxab.1, hxab.2, hC, hgC.continuousOn, ?_, ?_, intervalKernel_slopes hxab⟩
  · intro z hz
    apply hzero z
    intro hzC
    exact ((Ω.isOpen.frontier_eq ▸ hz).2)
      (connectedComponentIn_subset (Ω : Set _) x hzC)
  · intro t ht
    exact intervalTent_eq ht
  · intro y hy hyC
    exact hzero y hyC

theorem one_green_row (Ω : Domain 1)
    (hbounded : Bornology.IsBounded (Ω : Set (Space 1)))
    {x : Space 1} (hx : x ∈ Ω) :
    ∃ g : Space 1 → ℝ, IsGreenFunction Ω x g ∧ HasIntervalFormula Ω x g := by
  obtain ⟨a, b, hax, hxb, hC⟩ := one_component_interval Ω hbounded hx
  exact ⟨_, intervalTent_green Ω hx ⟨hax, hxb⟩ hC⟩

theorem linePoint_coord (y : Space 1) : linePoint (y 0) = y :=
  lineIsometry.apply_symm_apply y

theorem interval_formula_positive (Ω : Domain 1) {x : Space 1}
    {g : Space 1 → ℝ} (hg : HasIntervalFormula Ω x g)
    {y : Space 1} (hy : y ∈ connectedComponentIn (Ω : Set _) x) : 0 < g y := by
  obtain ⟨a, b, hax, hxb, hC, _, hformula, _, _⟩ := hg
  have hyab : y 0 ∈ Ioo a b := by
    rw [hC] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ht
  have he := hformula (y 0) ⟨hyab.1.le, hyab.2.le⟩
  rw [linePoint_coord] at he
  rw [he]
  exact intervalKernel_positive ⟨hax, hxb⟩ hyab

theorem interval_formula_symmetric (Ω : Domain 1) {x y : Space 1}
    {g k : Space 1 → ℝ} (_hx : x ∈ Ω) (hy : y ∈ connectedComponentIn (Ω : Set _) x)
    (hg : HasIntervalFormula Ω x g) (hk : HasIntervalFormula Ω y k) : g y = k x := by
  obtain ⟨a, b, hax, hxb, hCx, _, hgformula, _, _⟩ := hg
  obtain ⟨c, d, hcy, hyd, hCy, _, hkformula, _, _⟩ := hk
  have himage : lineIsometry '' Ioo a b = lineIsometry '' Ioo c d :=
    hCx.symm.trans ((connectedComponentIn_eq hy).trans hCy)
  have hI := (Set.image_injective.mpr lineIsometry.injective) himage
  have hac : a = c := by rw [← csInf_Ioo (hax.trans hxb), hI, csInf_Ioo (hcy.trans hyd)]
  have hbd : b = d := by rw [← csSup_Ioo (hax.trans hxb), hI, csSup_Ioo (hcy.trans hyd)]
  subst c d
  have hyab : y 0 ∈ Ioo a b := ⟨hcy, hyd⟩
  have he1 := hgformula (y 0) ⟨hyab.1.le, hyab.2.le⟩
  have he2 := hkformula (x 0) ⟨hax.le, hxb.le⟩
  rw [linePoint_coord] at he1 he2
  rw [he1, he2, intervalKernel_symmetric]

theorem construction_one_without_collar (Ω : Domain 1)
    (hbounded : Bornology.IsBounded (Ω : Set (Space 1))) :
    ∃ G : Space 1 → Space 1 → ℝ,
      (∀ x ∈ Ω, IsGreenFunction Ω x (G x) ∧ UniqueGreenFunction Ω x (G x)) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → G x y = G y x) ∧
      (∀ x ∈ Ω, ∀ y ∈ connectedComponentIn (Ω : Set _) x, x ≠ y → 0 < G x y) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, y ∉ connectedComponentIn (Ω : Set _) x → G x y = 0) ∧
      IntervalClause Ω G := by
  classical
  have hrows : ∀ x : Space 1, ∃ g : Space 1 → ℝ,
      x ∈ Ω → IsGreenFunction Ω x g ∧ HasIntervalFormula Ω x g := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨g, hg⟩ := one_green_row Ω hbounded hx
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose G hG using hrows
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hG x hx).1, green_unique (by omega : 1 ≤ 1) Ω hbounded hx (G x) (hG x hx).1⟩
  · intro x hx y hy hxy
    by_cases hyC : y ∈ connectedComponentIn (Ω : Set _) x
    · exact interval_formula_symmetric Ω hx hyC (hG x hx).2 (hG y hy).2
    · have hxC : x ∉ connectedComponentIn (Ω : Set _) y := by
        intro h
        apply hyC
        rw [← connectedComponentIn_eq h]
        exact mem_connectedComponentIn hy
      obtain ⟨a, b, _, _, _, _, _, hz, _⟩ := (hG x hx).2
      obtain ⟨c, d, _, _, _, _, _, hw, _⟩ := (hG y hy).2
      rw [hz y hy hyC, hw x hx hxC]
  · intro x hx y hy hxy
    exact interval_formula_positive Ω (hG x hx).2 hy
  · intro x hx y hy hyC
    obtain ⟨a, b, _, _, _, _, _, hz, _⟩ := (hG x hx).2
    exact hz y hy hyC
  · exact fun x hx => (hG x hx).2



theorem identity_energy_symmetric {n : ℕ} (Ω : Domain n) (u v : H ℝ Ω 1) :
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u v =
      ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) v u := by
  change (∫ x in Ω, ∑ i, ∑ j,
    (1 : Matrix (Fin n) (Fin n) ℝ) i j * hFirstDerivative u j x *
      star (hFirstDerivative v i x)) = _
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem firstDerivative_add {n : ℕ} (Ω : Domain n) (u v : H ℝ Ω 1) (i : Fin n) :
    hFirstDerivative (u+v) i = hFirstDerivative u i + hFirstDerivative v i := by
  rfl

theorem energy_laplacian_zero {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u : H ℝ Ω 1) (d : Lp ℝ Ω 2)
    (hd : NormalTrace.HasLaplacian Ω u d) (z : H10 ℝ Ω) :
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u z.val =
      -∫ x in Ω, d x * hZeroUnderlying Ω z x := by
  have h := P201.NormalTrace.bulkFunctional_zero hn Ω (hGradient u) d
    (P201.NormalTrace.gradientDivergence Ω u d hd) z
  rw [P201.NormalTrace.bulkFunctional_integral] at h
  have he : ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u z.val =
      ∫ x in Ω, inner ℝ (hGradient u x) (hGradient z.val x) := by
    apply integral_congr_ae
    have hu : (hGradient u : Space n → Space n) =ᵐ[domainMeasure Ω]
        (fun x => WithLp.toLp 2 (fun i => hFirstDerivative u i x)) := MemLp.coeFn_toLp _
    have hz : (hGradient z.val : Space n → Space n) =ᵐ[domainMeasure Ω]
        (fun x => WithLp.toLp 2 (fun i => hFirstDerivative z.val i x)) := MemLp.coeFn_toLp _
    filter_upwards [hu,hz] with x hx hx'
    rw [hx,hx']
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, star_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hi1 : Integrable (fun x => inner ℝ (hGradient u x) (hGradient z.val x))
      (domainMeasure Ω) := L2.integrable_inner (hGradient u) (hGradient z.val)
  have hi2 : Integrable (fun x => d x * hUnderlying Ω 1 z.val x)
      (domainMeasure Ω) :=
    (Lp.memLp d).integrable_mul (Lp.memLp (hUnderlying Ω 1 z.val))
  change (∫ x, inner ℝ (hGradient u x) (hGradient z.val x) +
    d x * hUnderlying Ω 1 z.val x ∂domainMeasure Ω) = 0 at h
  rw [integral_add hi1 hi2] at h
  exact he.trans (eq_neg_of_add_eq_zero_left h)

 theorem energy_add_left {n : ℕ} (Ω : Domain n) (u v w : H ℝ Ω 1) :
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) (u+v) w =
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u w +
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) v w := by
  have he (a b : H ℝ Ω 1) :
      ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) a b =
      ∫ x, ∑ i, hFirstDerivative a i x * hFirstDerivative b i x ∂domainMeasure Ω := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Matrix.one_apply]
  have hi (a b : H ℝ Ω 1) :
      Integrable (fun x => ∑ i, hFirstDerivative a i x * hFirstDerivative b i x)
        (domainMeasure Ω) := by
    exact integrable_finsetSum _ fun i _ =>
      memLp_one_iff_integrable.mp ((Lp.memLp (hFirstDerivative a i)).mul
        (Lp.memLp (hFirstDerivative b i)))
  rw [he, he, he, ← integral_add (hi u w) (hi v w)]
  apply integral_congr_ae
  have hae : ∀ᵐ x ∂domainMeasure Ω, ∀ i : Fin n,
      hFirstDerivative (u+v) i x = hFirstDerivative u i x + hFirstDerivative v i x :=
    ae_all_iff.mpr fun i => by
      rw [firstDerivative_add]
      exact Lp.coeFn_add _ _
  filter_upwards [hae] with x hx
  simp_rw [hx, add_mul]
  exact Finset.sum_add_distrib

 theorem affine_harmonic_reciprocity {n : ℕ} (Ω : Domain n)
     (F₁ F₂ : H ℝ Ω 1) (z₁ z₂ : H10 ℝ Ω)
     (h₁ : SmoothHarmonicLift.WeakHarmonic Ω (F₁ + z₁.val))
     (h₂ : SmoothHarmonicLift.WeakHarmonic Ω (F₂ + z₂.val)) :
     ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) F₁ z₂.val =
     ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) F₂ z₁.val := by
   have h₁₂ := h₁ z₂
   have h₂₁ := h₂ z₁
   change ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ))
     (F₁ + z₁.val) z₂.val = 0 at h₁₂
   change ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ))
     (F₂ + z₂.val) z₁.val = 0 at h₂₁
   rw [energy_add_left] at h₁₂ h₂₁
   rw [identity_energy_symmetric Ω z₂.val z₁.val] at h₂₁
   exact add_right_cancel (h₁₂.trans h₂₁.symm)


/-- A smooth parametrix cut off away from the pole pairs with any test
which is harmonic where the singular remainder is supported. -/
theorem localized_laplacian_pairing {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (x : Space n) (F : Space n → ℝ) (hF : ContDiffOn ℝ 2 F Ω)
    (φ : Test ℝ Ω)
    (he : ∀ y : Space n, F y * laplacian φ y =
      fundamentalKernel n (y - x) * laplacian φ y) :
    (∫ y, laplacian F y * φ y) = -φ x := by
  have hfL : LocallyIntegrableOn F Ω volume := hF.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hqL : LocallyIntegrableOn (laplacian F) Ω volume := (P201.MeanValues.laplacian_continuousOn Ω F hF).locallyIntegrableOn
    Ω.isOpen.measurableSet
  calc
    (∫ y, laplacian F y * φ y) =
        regularDistribution Ω (laplacian F) φ :=
      (P201.Weyl.regular_apply Ω _ hqL φ).symm
    _ = distributionLaplacian (regularDistribution Ω F) φ :=
      congrArg (fun U : Distribution ℝ Ω => U φ)
        (classical_laplacian_distribution Ω F hF).symm
    _ = ∫ y, F y * laplacian φ y := regular_laplacian_pairing Ω F hfL φ
    _ = ∫ y, fundamentalKernel n (y - x) * laplacian φ y := integral_congr_ae
      (ae_of_all _ he)
    _ = -φ x := translated_fundamental_pairing hn x φ
/-- Retain the weak affine data which are lost if only the continuous/H²
conclusion of harmonic lifting is recorded. The smooth bulk class is u−z. -/
theorem harmonic_lift_weak_data_conditional
    (harmonic_lift : SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (hm : 1 ≤ m) (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hC : HasCkBoundary Ω 2)
    (F : Space (m + 1) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ (h : Space (m + 1) → ℝ) (u F₁ : H ℝ Ω 1) (z : H10 ℝ Ω),
      MeanValues.IsHarmonic Ω h ∧ ContinuousOn h (closure (Ω : Set _)) ∧
      (∀ y ∈ frontier (Ω : Set _), h y = F y) ∧
      (∃ w : H ℝ Ω 2, (hUnderlying Ω 2 w : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω] h) ∧
      (hUnderlying Ω 1 u : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω] h ∧
      (hUnderlying Ω 1 F₁ : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω] F ∧
      u = F₁ + z.val ∧ SmoothHarmonicLift.WeakHarmonic Ω u := by
  let g : C(frontier (Ω : Set (Space (m+1))), ℝ) :=
    ⟨fun y => F y, hF.continuous.comp continuous_subtype_val⟩
  obtain ⟨h, hext, _, hlift⟩ := harmonic_lift hm Ω hb hC g
  obtain ⟨u, ⟨⟨z,hz⟩,hweak⟩, hu, hw, _⟩ := hlift F
    ⟨univ,isOpen_univ,subset_univ _,hF.contDiffOn⟩ (fun _ => rfl)
  refine ⟨h,u,u-z.val,z,hext.1,hext.2.1,?_,hw,hu,?_,?_,hweak⟩
  · intro y hy
    exact hext.2.2 ⟨y,hy⟩
  · rw [map_sub]
    filter_upwards [Lp.coeFn_sub (hUnderlying Ω 1 u) (hUnderlying Ω 1 z.val),hz] with y hy hy'
    rw [hy]
    change hUnderlying Ω 1 u y - hZeroUnderlying Ω z y = F y
    rw [hy']
    exact add_sub_cancel_right _ _
  · exact (sub_add_cancel _ _).symm
/-- The proved construction in all positive dimensions: unique Green rows,
the componentwise signs, the full interval formula and symmetry in dimension
one, and harmonic corrections with actual H² collar classes above dimension
one. This auxiliary statement omits the general symmetry and normal-trace
clauses, which are supplied by the final `construction_conditional`. -/
theorem green_kernel_all_dimensions_conditional
    (harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (Ω : Domain (m + 1))
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasCkBoundary Ω 2) :
    ∃ G : Space (m + 1) → Space (m + 1) → ℝ,
      (∀ x ∈ Ω, IsGreenFunction Ω x (G x) ∧ UniqueGreenFunction Ω x (G x)) ∧
      (∀ x ∈ Ω, ∀ y ∈ connectedComponentIn (Ω : Set _) x, x ≠ y → 0 < G x y) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, y ∉ connectedComponentIn (Ω : Set _) x → G x y = 0) ∧
      (1 ≤ m → ∀ x ∈ Ω, HasHarmonicCorrection Ω x (G x) ∧
        ∀ r : ℝ, 0 < r → ∃ w : H ℝ (collar Ω x r) 2,
          (hUnderlying (collar Ω x r) 2 w : Space (m + 1) → ℝ)
            =ᵐ[domainMeasure (collar Ω x r)] G x) ∧
      IntervalClause Ω G ∧
      (m = 0 → ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → G x y = G y x) := by
  cases m with
  | zero =>
    obtain ⟨G, hG, hsym, hpos, hzero, hinterval⟩ :=
      construction_one_without_collar Ω hbounded
    exact ⟨G, hG, hpos, hzero, by omega, hinterval, fun _ => hsym⟩
  | succ k =>
    obtain ⟨G, hG, _, hpos, hzero⟩ := green_kernel_signs_conditional
      harmonic_lift (Nat.succ_le_succ (Nat.zero_le k)) Ω hbounded hboundary
    refine ⟨G, fun x hx => ⟨(hG x hx).1, (hG x hx).2.1⟩, hpos, hzero,
      ?_, trivial, by omega⟩
    intro _ x hx
    exact ⟨(hG x hx).2.2, fun r hr => green_collar_h2 Ω hbounded (G x) (hG x hx).2.2 hr⟩

/-- A bump localized into an open region where f is smooth defines a genuine
compact smooth test, with a full germ equal to f on its inner ball. -/
theorem cutoff_smooth_test {n : ℕ} (Ω V : Domain n) (x : Space n)
    (η : ContDiffBump x)
    (hηΩ : tsupport η ⊆ (Ω : Set _)) (hηV : tsupport η ⊆ (V : Set _))
    (f : Space n → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) :
    ∃ φ : Test ℝ Ω,
      (∀ y, φ y = η y * f y) ∧
      ∀ y ∈ ball x η.rIn, (φ : Space n → ℝ) =ᶠ[𝓝 y] f := by
  let p := fun y => η y * f y
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport η
    · exact η.contDiffAt.mul (hf.contDiffAt (V.isOpen.mem_nhds (hηV hy)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [p,hz]
  have hpcomp : HasCompactSupport p := η.hasCompactSupport.mul_right
  have hpsupp : tsupport p ⊆ (Ω : Set _) :=
    tsupport_mul_subset_left.trans hηΩ
  let φ : Test ℝ Ω := ⟨p,hp,hpcomp,hpsupp⟩
  refine ⟨φ,fun _ => rfl,?_⟩
  intro y hy
  filter_upwards [η.eventuallyEq_one_of_mem_ball hy] with z hz
  simp [φ,p,hz]

/-- With a nested cutoff, harmonicity is retained on the inner ball at the
level of the actual coordinate Laplacian of the resulting test. -/
theorem cutoff_harmonic_test {n : ℕ} (Ω V : Domain n) (x : Space n)
    (η : ContDiffBump x)
    (hηΩ : tsupport η ⊆ (Ω : Set _)) (hηV : tsupport η ⊆ (V : Set _))
    (f : Space n → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V)
    (hh : MeanValues.IsHarmonic V f) :
    ∃ φ : Test ℝ Ω,
      (∀ y, φ y = η y * f y) ∧
      ∀ y ∈ ball x η.rIn, laplacian φ y = 0 := by
  obtain ⟨φ,hφ,he⟩ := cutoff_smooth_test Ω V x η hηΩ hηV f hf
  refine ⟨φ,hφ,fun y hy => ?_⟩
  have hyV : y ∈ V := hηV (by
    rw [η.tsupport_eq]
    exact mem_closedBall.mpr (le_trans (mem_ball.mp hy).le (le_of_lt η.rIn_lt_rOut)))
  exact (P201.Weyl.laplacian_eq_of_eventuallyEq (he y hy)).trans (hh.2 y hyV)

/-- The cutoff parametrix evaluates harmonic functions without sphere limits.
The smooth F equals the normalized Φ outside the smaller closed ball. -/
theorem localized_harmonic_evaluation {n : ℕ} (hn : 1 ≤ n)
    (Ω V : Domain n) (x : Space n) (r : ℝ) (hr : 0 ≤ r)
    (η : ContDiffBump x) (hrr : r < η.rIn)
    (hηΩ : tsupport η ⊆ (Ω : Set _)) (hηV : tsupport η ⊆ (V : Set _))
    (f F : Space n → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V)
    (hh : MeanValues.IsHarmonic V f) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFoutside : ∀ y ∉ closedBall x r, F y = fundamentalKernel n (y-x)) :
    (∫ y, laplacian F y * f y) = -f x := by
  obtain ⟨φ,hφ,hφΔ⟩ := cutoff_harmonic_test Ω V x η hηΩ hηV f hf hh
  have hqzero (y : Space n) (hy : y ∉ closedBall x r) : laplacian F y = 0 := by
    have hlocal : F =ᶠ[𝓝 y] (fun z => fundamentalKernel n (z-x)) := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      exact hFoutside z hz
    have hyx : y ≠ x := by
      intro he
      subst y
      exact hy (mem_closedBall_self hr)
    have hhPhi := translated_fundamental_harmonic hn (⊤ : Domain n) x
    exact (P201.Weyl.laplacian_eq_of_eventuallyEq hlocal).trans
      (hhPhi.2 y ⟨mem_univ _,by simpa using hyx⟩)
  have hpEq (y : Space n) (hy : y ∈ closedBall x r) : φ y = f y := by
    rw [hφ,η.one_of_mem_closedBall (closedBall_subset_closedBall hrr.le hy),one_mul]
  have htest (y : Space n) : F y * laplacian φ y =
      fundamentalKernel n (y-x) * laplacian φ y := by
    by_cases hy : y ∈ closedBall x r
    · have hyinner : y ∈ ball x η.rIn := lt_of_le_of_lt (mem_closedBall.mp hy) hrr
      rw [hφΔ y hyinner,mul_zero,mul_zero]
    · rw [hFoutside y hy]
  have hev := localized_laplacian_pairing hn Ω x F (hF.of_le (by simp)).contDiffOn φ htest
  have hqPair : (∫ y, laplacian F y * f y) = ∫ y, laplacian F y * φ y := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ closedBall x r
    · rw [hpEq y hy]
    · rw [hqzero y hy,zero_mul,zero_mul]
  exact hqPair.trans (hev.trans (congrArg Neg.neg (hpEq x (mem_closedBall_self hr))))

/-- The actual smooth lift formed by excising the singularity with a bump. -/
theorem cutoff_fundamental_smooth {n : ℕ} (x : Space n) (β : ContDiffBump x) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (1-β y) * fundamentalKernel n (y-x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y=x
  · subst y
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [β.eventuallyEq_one] with z hz
    simp [hz]
  · exact (contDiffAt_const.sub β.contDiffAt).mul
      (translated_fundamental_contDiffAt x hy)

/-- Exact harmonic evaluation by the Laplacian of a cut off fundamental
solution. All cutoff, test-function, and normalization bridges are proved. -/
theorem cutoff_fundamental_evaluation {n : ℕ} (hn : 1 ≤ n)
    (Ω V : Domain n) (x : Space n) (β η : ContDiffBump x)
    (hβη : β.rOut < η.rIn)
    (hηΩ : tsupport η ⊆ (Ω : Set _)) (hηV : tsupport η ⊆ (V : Set _))
    (f : Space n → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V)
    (hh : MeanValues.IsHarmonic V f) :
    (∫ y, laplacian (fun z => (1-β z) * fundamentalKernel n (z-x)) y * f y) = -f x := by
  apply localized_harmonic_evaluation hn Ω V x β.rOut β.rOut_pos.le η hβη hηΩ hηV f _ hf hh
    (cutoff_fundamental_smooth x β)
  intro y hy
  have hz : β y = 0 := β.zero_of_le_dist (not_le.mp hy).le
  simp [hz]
open P201Specs P201Specs.GreenConstruction P102.Trace.Ordinary
theorem hilbert_representative_of_classical_memLp {n : ℕ} (Ω : Domain n)
    (k : ℕ) (f : Space n → ℝ) (hf : ContDiffOn ℝ k f Ω)
    (hα : ∀ α : MultiIndex n, α.card ≤ k → MemLp (multiPartial f α) 2 (domainMeasure Ω)) :
    ∃ u : H ℝ Ω k, (hUnderlying Ω k u : Space n → ℝ) =ᵐ[domainMeasure Ω] f := by
  have h0 : MemLp f 2 (domainMeasure Ω) := by
    simpa [multiPartial, P102.U4.multiPartial, P102.U4.partialWord] using hα 0 (by simp)
  have heq (g : Space n → ℝ) (hg : MemLp g 2 (domainMeasure Ω)) :
      regularDistribution Ω (hg.toLp g) = regularDistribution Ω g := by
    apply (P102.U4.regular_injectivity n ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _) (locallyIntegrableOn_of_locallyIntegrable_restrict
        (hg.locallyIntegrable (by norm_num)))).mpr
    exact hg.coeFn_toLp
  have hder : P102.U4.HasSobolevDerivatives Ω k 2 (h0.toLp f) := by
    intro α hcard
    refine ⟨(hα α hcard).toLp (multiPartial f α), ?_⟩
    change distributionDerivative α (regularDistribution Ω (h0.toLp f)) =
      regularDistribution Ω ((hα α hcard).toLp (multiPartial f α))
    rw [heq f h0, heq (multiPartial f α) (hα α hcard)]
    exact P102.U4.derivative_classicalCompatibility n ℝ Ω α f (hf.of_le (by exact_mod_cast hcard))
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range Ω k 2) (h0.toLp f)).mpr hder
  refine ⟨(hToW ℝ Ω k).symm w, ?_⟩
  have hh : hUnderlying Ω k ((hToW ℝ Ω k).symm w) = h0.toLp f := by
    change P102.U4.sobolevUnderlying ((hToW ℝ Ω k) ((hToW ℝ Ω k).symm w)) = _
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  rw [hh]
  exact h0.coeFn_toLp

theorem intervalTent_firstDerivative_values (Ω : Domain 1) {x : Space 1}
    (_hx : x ∈ Ω) {a b : ℝ} (hxab : x 0 ∈ Ioo a b)
    (hC : connectedComponentIn (Ω : Set _) x = linePoint '' Ioo a b)
    {y : Space 1} (hy : y ∈ Ω) (hyx : y ≠ x) :
    multiPartial (fun z : Space 1 => intervalTent a b (x 0) (z 0)) ({0} : MultiIndex 1) y =
      (b - x 0) / (b - a) ∨
    multiPartial (fun z : Space 1 => intervalTent a b (x 0) (z 0)) ({0} : MultiIndex 1) y =
      -(x 0 - a) / (b - a) ∨
    multiPartial (fun z : Space 1 => intervalTent a b (x 0) (z 0)) ({0} : MultiIndex 1) y = 0 := by
  let g := fun z : Space 1 => intervalTent a b (x 0) (z 0)
  have hc : Continuous (fun z : Space 1 => z 0) := (EuclideanSpace.proj 0).continuous
  by_cases hyC : y ∈ connectedComponentIn (Ω : Set _) x
  · have hyab : y 0 ∈ Ioo a b := by
      rw [hC] at hyC
      obtain ⟨t, ht, rfl⟩ := hyC
      exact ht
    have hcoord : y 0 ≠ x 0 := fun h => hyx (lineIsometry.symm.injective h)
    rcases lt_or_gt_of_ne hcoord with hlt | hgt
    · left
      let L : Space 1 →L[ℝ] ℝ := ((b - x 0) / (b - a)) • EuclideanSpace.proj 0
      have he : g =ᶠ[𝓝 y] (fun z => L z - a * ((b - x 0) / (b - a))) := by
        filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hyab),
          hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt)] with z hz hzlt
        change intervalTent a b (x 0) (z 0) = _
        rw [intervalTent_eq ⟨hz.1.le, hz.2.le⟩, intervalKernel_left hzlt.le]
        change (z 0 - a) * (b - x 0) / (b - a) = _
        change (z 0 - a) * (b - x 0) / (b - a) =
          ((b - x 0) / (b - a)) * z 0 - a * ((b - x 0) / (b - a))
        ring
      have heD := (P102.U4.partialWord_eventuallyEq he [0]).eq_of_nhds
      simp only [multiPartial, P102.U4.multiPartial, Multiset.sort_singleton]
      change P102.U4.partialWord g [0] y = _
      rw [heD]
      simp only [P102.U4.partialWord, fderiv_sub_const]
      change (fderiv ℝ L y) (P102.U4.coordinateVector 1 0) = _
      rw [L.fderiv]
      simp [L, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]
    · right; left
      let L : Space 1 →L[ℝ] ℝ := (-(x 0 - a) / (b - a)) • EuclideanSpace.proj 0
      have he : g =ᶠ[𝓝 y] (fun z => L z + b * ((x 0 - a) / (b - a))) := by
        filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hyab),
          hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hgt)] with z hz hzgt
        change intervalTent a b (x 0) (z 0) = _
        rw [intervalTent_eq ⟨hz.1.le, hz.2.le⟩, intervalKernel_right hzgt.le]
        change (x 0 - a) * (b - z 0) / (b - a) =
          (-(x 0 - a) / (b - a)) * z 0 + b * ((x 0 - a) / (b - a))
        ring
      have heD := (P102.U4.partialWord_eventuallyEq he [0]).eq_of_nhds
      simp only [multiPartial, P102.U4.multiPartial, Multiset.sort_singleton]
      change P102.U4.partialWord g [0] y = _
      rw [heD]
      simp only [P102.U4.partialWord, fderiv_add_const]
      change (fderiv ℝ L y) (P102.U4.coordinateVector 1 0) = _
      rw [L.fderiv]
      simp [L, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]
  · right; right
    have hyncl : y ∉ closure (connectedComponentIn (Ω : Set _) x) := fun h =>
      hyC (closure_component_inter_domain Ω x ⟨h, hy⟩)
    have he : g =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hyncl] with z hz
      have hzab : z 0 ∉ Ioo a b := by
        intro hab
        apply hz
        apply subset_closure
        rw [hC]
        exact ⟨z 0, hab, linePoint_coord z⟩
      exact intervalTent_zero hxab hzab
    have heD := (P102.U4.partialWord_eventuallyEq he [0]).eq_of_nhds
    simp only [multiPartial, P102.U4.multiPartial, Multiset.sort_singleton]
    change P102.U4.partialWord g [0] y = _
    rw [heD]
    simp [P102.U4.partialWord]

theorem intervalTent_hilbert_representative (Ω V : Domain 1)
    (hbounded : Bornology.IsBounded (V : Set (Space 1)))
    {x : Space 1} (hx : x ∈ Ω) {a b : ℝ} (hxab : x 0 ∈ Ioo a b)
    (hC : connectedComponentIn (Ω : Set _) x = linePoint '' Ioo a b)
    (hV : V ≤ punctured Ω x) (k : ℕ) (hk : k ≤ 2) :
    ∃ u : H ℝ V k, (hUnderlying V k u : Space 1 → ℝ) =ᵐ[domainMeasure V]
      (fun y => intervalTent a b (x 0) (y 0)) := by
  let g := fun y : Space 1 => intervalTent a b (x 0) (y 0)
  have hg := (intervalTent_green Ω hx hxab hC).1
  have hgS : ContDiffOn ℝ (⊤ : ℕ∞) g V := hg.2.2.1.mono hV
  have hgC : Continuous g := (intervalTent_continuous a b (x 0)).comp
    (EuclideanSpace.proj 0).continuous
  have hc : IsCompact (closure (V : Set (Space 1))) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hbounded.closure⟩
  let : IsFiniteMeasure (domainMeasure V) := ⟨by
    simpa [domainMeasure, P201Specs.domainMeasure] using
      (measure_mono (μ := volume) (subset_closure : (V : Set (Space 1)) ⊆ closure (V : Set _))).trans_lt hc.measure_lt_top⟩
  have hg0 : MemLp g 2 (domainMeasure V) := by
    obtain ⟨C, hC⟩ := hc.bddAbove_image hgC.continuousOn.norm
    exact MemLp.of_bound hgC.aestronglyMeasurable C
      ((ae_restrict_mem V.isOpen.measurableSet).mono (fun y hy => hC ⟨y, subset_closure hy, rfl⟩))
  apply hilbert_representative_of_classical_memLp V k g (hgS.of_le (by simp))
  intro α hα
  have hrep : α = Multiset.replicate α.card 0 :=
    Multiset.eq_replicate_card.mpr (fun i _ => Subsingleton.elim _ _)
  have hcα : α.card = 0 ∨ α.card = 1 ∨ α.card = 2 := by omega
  rcases hcα with hcard | hcard | hcard
  · have hα0 : α = 0 := by simpa [hcard] using hrep
    simpa [hα0, multiPartial, P102.U4.multiPartial, P102.U4.partialWord] using hg0
  · have hα1 : α = {0} := by simpa [hcard] using hrep
    rw [hα1]
    have hdC : ContinuousOn (multiPartial g ({0} : MultiIndex 1)) V := by
      simpa [multiPartial, P102.U4.multiPartial] using
        (P102.U4.partialWord_contDiffOn V ((hgS.of_le (by simp) : ContDiffOn ℝ (1 : ℕ) g V))
        [0] 0 (by simp)).continuousOn
    apply MemLp.of_bound (hdC.aestronglyMeasurable V.isOpen.measurableSet)
      (|(b - x 0) / (b - a)| + |-(x 0 - a) / (b - a)|)
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with y hy
    rcases intervalTent_firstDerivative_values Ω hx hxab hC (hV hy).1
      (by simpa using (hV hy).2) with he | he | he
    · rw [he, Real.norm_eq_abs]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [he, Real.norm_eq_abs]
      exact le_add_of_nonneg_left (abs_nonneg _)
    · rw [he, norm_zero]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · have hα2 : α = {0, 0} := by simpa [hcard, Multiset.replicate_succ] using hrep
    have hezero : multiPartial g α =ᵐ[domainMeasure V] (fun _ => 0) := by
      filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with y hy
      have hl := hg.2.2.2.1.2 y (hV hy)
      simpa [laplacian, P201Specs.laplacian, hα2] using hl
    exact (memLp_congr_ae hezero).mpr MemLp.zero

theorem interval_formula_hilbert_representative (Ω V : Domain 1)
    (hbounded : Bornology.IsBounded (V : Set (Space 1)))
    {x : Space 1} (hx : x ∈ Ω) {g : Space 1 → ℝ} (hg : HasIntervalFormula Ω x g)
    (hV : V ≤ punctured Ω x) (k : ℕ) (hk : k ≤ 2) :
    ∃ u : H ℝ V k, (hUnderlying V k u : Space 1 → ℝ) =ᵐ[domainMeasure V] g := by
  obtain ⟨a, b, hax, hxb, hC, _, hformula, hzero, _⟩ := hg
  obtain ⟨u, hu⟩ := intervalTent_hilbert_representative Ω V hbounded hx ⟨hax, hxb⟩ hC hV k hk
  refine ⟨u, hu.trans ?_⟩
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with y hy
  by_cases hyC : y ∈ connectedComponentIn (Ω : Set _) x
  · have hyab : y 0 ∈ Ioo a b := by
      rw [hC] at hyC
      obtain ⟨t, ht, rfl⟩ := hyC
      exact ht
    rw [intervalTent_eq ⟨hyab.1.le, hyab.2.le⟩]
    have he := hformula (y 0) ⟨hyab.1.le, hyab.2.le⟩
    rw [linePoint_coord] at he
    exact he.symm
  · have hyab : y 0 ∉ Ioo a b := by
      intro hab
      exact hyC (hC ▸ ⟨y 0, hab, linePoint_coord y⟩)
    rw [intervalTent_zero ⟨hax, hxb⟩ hyab, hzero y (hV hy).1 hyC]

open P201Specs P201Specs.GreenConstruction
open P201Specs.NormalTrace

lemma geometric_normal_component_le {m : ℕ} (Ω : Domain (m + 1))
    (ν : Space (m + 1) → Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν) (i : Fin (m + 1)) :
    ∀ᵐ y ∂boundaryMeasure Ω, ‖ν y i‖ ≤ 1 := by
  filter_upwards [hν.2] with y hy
  have hn1 : ‖ν y‖ = 1 := by simpa only [LinearIsometryEquiv.norm_map] using hy.1
  exact (PiLp.norm_apply_le (ν y) i).trans_eq hn1

lemma trace_mul_normal_memLp {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (ν : Space (m + 1) → Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (b : Hhalf Ω hΩ) (i : Fin (m + 1)) :
    MemLp (fun y => Trace.inclusion Ω hΩ b y * ν y i) 2 (boundaryMeasure Ω) := by
  apply (Lp.memLp (Trace.inclusion Ω hΩ b)).of_le_mul
    ((Lp.aestronglyMeasurable _).mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) i).continuous.comp_aestronglyMeasurable hν.1)) (c := 1)
  filter_upwards [geometric_normal_component_le Ω ν hν i] with y hy
  change ‖Trace.inclusion Ω hΩ b y * ν y i‖ ≤ 1 * ‖Trace.inclusion Ω hΩ b y‖
  rw [norm_mul, one_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hy

lemma divergence_coordinate_field {n : ℕ} (f : Space n → ℝ) (hf : Differentiable ℝ f)
    (i : Fin n) (y : Space n) :
    divergence (fun z => f z • coordinate n i) y = fderiv ℝ f y (coordinate n i) := by
  change (∑ j : Fin n, fderiv ℝ (fun z => (f z • coordinate n i) j) y (coordinate n j)) = _
  have he (j : Fin n) : (fun z => (f z • coordinate n i) j) =
      fun z => f z * if i = j then 1 else 0 := by
    funext z
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
  simp_rw [he]
  simp only [fderiv_mul_const (hf y)]
  calc
    _ = ((if i = i then (1:ℝ) else 0) • fderiv ℝ f y) (coordinate n i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    _ = _ := by simp

lemma inner_coordinate {n : ℕ} (i : Fin n) (z : Space n) :
    inner ℝ (coordinate n i) z = z i :=
  EuclideanSpace.basisFun_inner (Fin n) ℝ z i

lemma smooth_first_derivative_ae {m : ℕ} (Ω : Domain (m + 1)) (a : H ℝ Ω 1)
    (f : Space (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ha : (hUnderlying Ω 1 a : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] f)
    (i : Fin (m + 1)) :
    (hFirstDerivative a i : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω]
      fun y => fderiv ℝ f y (coordinate (m + 1) i) := by
  have hg := P201.NormalTrace.smooth_gradient_ae Ω a f hf ha
  have hva : (hGradient a : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω]
      fun y => WithLp.toLp 2 (fun j => hFirstDerivative a j y) := MemLp.coeFn_toLp _
  filter_upwards [hg, hva] with y hy hyv
  exact (congrArg (fun z : Space (m + 1) => z i) hyv).symm.trans
    (congrArg (fun z : Space (m + 1) => z i) hy)

/-- Coordinate Green identity for arbitrary H¹ factors, with their physical
boundary traces. Density is applied in one scalar field at a time. -/
theorem h1_scalar_green_identity {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) :
    ∃ ν : Space (m + 1) → Space (m + 1),
      P201Specs.SmoothFlux.IsGeometricNormalField Ω ν ∧
      ∀ (D : TraceData Ω hΩ) (i : Fin (m + 1)) (a b : H ℝ Ω 1),
        Integrable (fun y => Trace.inclusion Ω hΩ (D.trace b) y *
          Trace.inclusion Ω hΩ (D.trace a) y * ν y i) (boundaryMeasure Ω) ∧
        (∫ y in Ω, hUnderlying Ω 1 a y * hFirstDerivative b i y +
          hFirstDerivative a i y * hUnderlying Ω 1 b y) =
        ∫ y, Trace.inclusion Ω hΩ (D.trace b) y *
          Trace.inclusion Ω hΩ (D.trace a) y * ν y i ∂boundaryMeasure Ω := by
  obtain ⟨ν, hν, hsmooth⟩ := P201.NormalTrace.smoothAgreement Ω hΩ
  refine ⟨ν, hν, ?_⟩
  intro D i a b
  have htm := trace_mul_normal_memLp Ω hΩ ν hν (D.trace b) i
  let t : Trace.BoundaryL2 Ω := htm.toLp _
  let A : H ℝ Ω 1 →L[ℝ] ℝ :=
    ((innerSL ℝ (hFirstDerivative b i)).comp (hUnderlying Ω 1)) +
    ((innerSL ℝ (hUnderlying Ω 1 b)).comp (P201.InteriorTesting.firstDerivativeMap Ω i))
  let B : H ℝ Ω 1 →L[ℝ] ℝ :=
    ((innerSL ℝ t).comp (Trace.inclusion Ω hΩ)).comp D.trace
  have hA (a : H ℝ Ω 1) : A a = ∫ y in Ω,
      hUnderlying Ω 1 a y * hFirstDerivative b i y +
      hFirstDerivative a i y * hUnderlying Ω 1 b y := by
    rw [integral_add ((Lp.memLp _).integrable_mul (Lp.memLp _))
      ((Lp.memLp _).integrable_mul (Lp.memLp _))]
    simp only [A, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      P201.InteriorTesting.firstDerivativeMap_apply, L2.inner_def,
      RCLike.inner_apply, RCLike.conj_to_real]
  have hB (a : H ℝ Ω 1) : B a = ∫ y,
      Trace.inclusion Ω hΩ (D.trace b) y * Trace.inclusion Ω hΩ (D.trace a) y * ν y i
        ∂boundaryMeasure Ω := by
    simp only [B, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [htm.coeFn_toLp] with y hy
    simp only [RCLike.inner_apply, RCLike.conj_to_real]
    rw [hy]
    ring
  have heq (a : H ℝ Ω 1) : A a = B a := by
    let e := hToW ℝ Ω 1
    let A' := A.comp e.symm.toContinuousLinearMap
    let B' := B.comp e.symm.toContinuousLinearMap
    have hc : IsClosed {w : W ℝ Ω 1 2 | A' w = B' w} := isClosed_eq A'.continuous B'.continuous
    have hs : (P102.Trace.Ordinary.smoothRestrictionSubmodule ℝ Ω 2 : Set (W ℝ Ω 1 2)) ⊆
        {w | A' w = B' w} := by
      rintro w ⟨f, hf, hw⟩
      let z := e.symm w
      have hz : (hUnderlying Ω 1 z : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] f := by
        change P102.U4.sobolevUnderlying (e (e.symm w)) =ᵐ[_] f
        simpa using hw
      let F₀ := fun y => f y • coordinate (m + 1) i
      have hF : ContDiffOn ℝ 1 F₀ univ :=
        ((hf.of_le (by simp)).smul contDiff_const).contDiffOn
      obtain ⟨F, d, hFa, hda, hd, hflux⟩ := hsmooth D univ F₀
        isOpen_univ (subset_univ _) hF
      let τ := P201.NormalTrace.normalTrace D F d
      have hτ := P201.NormalTrace.normalTrace_pairing Ω hΩ D F d hd
      have hI := (hflux τ hτ (D.trace b)).2
      rw [hτ b] at hI
      change A z = B z
      rw [hA, hB]
      have hdz := smooth_first_derivative_ae Ω z f hf hz i
      have hgb : (hGradient b : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω]
          fun y => WithLp.toLp 2 (fun j => hFirstDerivative b j y) := MemLp.coeFn_toLp _
      calc
        _ = ∫ y in Ω, inner ℝ (F y) (hGradient b y) + d y * hUnderlying Ω 1 b y := by
          apply integral_congr_ae
          filter_upwards [hz, hdz, hFa, hda, hgb] with y hy hz' hyF hyd hyg
          rw [hy, hz', hyF, hyd, hyg]
          change f y * hFirstDerivative b i y + fderiv ℝ f y (coordinate (m + 1) i) *
              hUnderlying Ω 1 b y =
            inner ℝ (f y • coordinate (m + 1) i) (WithLp.toLp 2 (fun j => hFirstDerivative b j y)) +
              divergence (fun z => f z • coordinate (m + 1) i) y * hUnderlying Ω 1 b y
          rw [divergence_coordinate_field f (hf.differentiable (by simp)) i y]
          simp only [inner_smul_left, inner_coordinate, RCLike.conj_to_real]

        _ = ∫ y, Trace.inclusion Ω hΩ (D.trace b) y * inner ℝ (F₀ y) (ν y)
            ∂boundaryMeasure Ω := hI
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [D.smooth z f hf hz] with y hy
          rw [hy]
          change Trace.inclusion Ω hΩ (D.trace b) y *
              inner ℝ (f y • coordinate (m + 1) i) (ν y) =
            Trace.inclusion Ω hΩ (D.trace b) y * f y * ν y i
          simp only [inner_smul_left, inner_coordinate, RCLike.conj_to_real]
          ring
    have hdense := P102.Trace.Ordinary.smooth_restrictions_dense
      P102.Sobolev.Extension.lipschitz_ambient_density (graphFrame m) Ω hΩ ℝ 2 (by norm_num)
    have he := closure_minimal hs hc (hdense (e a))
    simpa [A', B', e] using he
  refine ⟨?_, ?_⟩
  · have hm := (Lp.memLp (Trace.inclusion Ω hΩ (D.trace a))).integrable_mul htm
    convert hm using 1
    funext y
    change Trace.inclusion Ω hΩ (D.trace b) y * Trace.inclusion Ω hΩ (D.trace a) y * ν y i =
      Trace.inclusion Ω hΩ (D.trace a) y * (Trace.inclusion Ω hΩ (D.trace b) y * ν y i)
    ring
  · rw [← hA, ← hB]
    exact heq a

/-- The regular distribution map on actual L² classes. -/
def regularLpMap {n : ℕ} (U : Domain n) : Lp ℝ U 2 →ₗ[ℝ] Distribution ℝ U where
  toFun u := regularDistribution U u
  map_add' u v := by
    ext φ
    simp only [P102.U4.regularLp_pairing U 2, ContinuousLinearMap.map_add, add_apply]
  map_smul' r u := by
    ext φ
    simp only [P102.U4.regularLp_pairing U 2, ContinuousLinearMap.map_smul,
      smul_apply, RingHom.id_apply]

/-- H¹ classes realizing a harmonic function's gradient have zero summed
weak divergence as an actual L² class. -/
lemma harmonic_gradient_divergence_zero {n : ℕ} (U : Domain n)
    (u : H ℝ U 1) (v : Fin n → H ℝ U 1)
    (hv : ∀ i, (hUnderlying U 1 (v i) : Space n → ℝ) =ᵐ[domainMeasure U]
      fun y => hGradient u y i) (hu : HasLaplacian U u 0) :
    ∑ i, hFirstDerivative (v i) i = 0 := by
  have hga : (hGradient u : Space n → Space n) =ᵐ[domainMeasure U]
      fun y => WithLp.toLp 2 (fun j => hFirstDerivative u j y) := MemLp.coeFn_toLp _
  have hvi (i : Fin n) : hUnderlying U 1 (v i) = hFirstDerivative u i := by
    apply Lp.ext
    filter_upwards [hv i, hga] with y hy hyg
    exact hy.trans (congrArg (fun z : Space n => z i) hyg)
  have he (i : Fin n) : regularDistribution U (hFirstDerivative (v i) i) =
      distributionDerivative {i, i} (regularDistribution U (hUnderlying U 1 u)) := by
    have h1 := P201.hilbertDerivativeDistribution U 1 (v i) ⟨{i}, by simp⟩
    change distributionDerivative {i} (regularDistribution U (hUnderlying U 1 (v i))) =
      regularDistribution U (hFirstDerivative (v i) i) at h1
    rw [hvi] at h1
    have h2 := P201.hilbertDerivativeDistribution U 1 u ⟨{i}, by simp⟩
    change distributionDerivative {i} (regularDistribution U (hUnderlying U 1 u)) =
      regularDistribution U (hFirstDerivative u i) at h2
    calc
      _ = distributionDerivative {i} (regularDistribution U (hFirstDerivative u i)) := h1.symm
      _ = distributionDerivative {i} (distributionDerivative {i}
          (regularDistribution U (hUnderlying U 1 u))) := congrArg (distributionDerivative {i}) h2.symm
      _ = _ := (P102.U4.derivative_add n ℝ U {i} {i} _).symm
  apply P102.U4.regularLp_injective U 2
  calc
    _ = (regularLpMap U) (∑ i, hFirstDerivative (v i) i) := rfl
    _ = ∑ i, regularDistribution U (hFirstDerivative (v i) i) := map_sum _ _ _
    _ = distributionLaplacian (regularDistribution U (hUnderlying U 1 u)) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = _ := hu

/-- Harmonic H¹ fields whose gradient components belong to H¹ have the
geometric normal trace supplied by the scalar trace of those components. -/
theorem harmonic_h1_gradient_normal_trace {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (u : H ℝ Ω 1) (v : Fin (m + 1) → H ℝ Ω 1)
    (hv : ∀ i, (hUnderlying Ω 1 (v i) : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω]
      fun y => hGradient u y i) (hu : HasLaplacian Ω u 0) :
    ∃ ν : Space (m + 1) → Space (m + 1),
      P201Specs.SmoothFlux.IsGeometricNormalField Ω ν ∧
      ∀ D : TraceData Ω hΩ, ∃ τ : HminusHalf Ω hΩ,
        Pairing D (hGradient u) 0 τ ∧
        (∀ σ : HminusHalf Ω hΩ, Pairing D (hGradient u) 0 σ → σ = τ) ∧
        ∀ b : Hhalf Ω hΩ,
          Integrable (fun y => Trace.inclusion Ω hΩ b y *
            ∑ i, Trace.inclusion Ω hΩ (D.trace (v i)) y * ν y i) (boundaryMeasure Ω) ∧
          τ b = ∫ y, Trace.inclusion Ω hΩ b y *
            ∑ i, Trace.inclusion Ω hΩ (D.trace (v i)) y * ν y i ∂boundaryMeasure Ω := by
  obtain ⟨ν, hν, hscalar⟩ := h1_scalar_green_identity Ω hΩ
  have hdiv := harmonic_gradient_divergence_zero Ω u v hv hu
  have hdiva : ∀ᵐ y ∂domainMeasure Ω, ∑ i, hFirstDerivative (v i) i y = 0 := by
    have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i => hFirstDerivative (v i) i)
    rw [hdiv] at hsum
    filter_upwards [hsum, Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with y hy hy0
    exact hy.symm.trans hy0
  have hgu : (hGradient u : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω]
      fun y => WithLp.toLp 2 (fun j => hFirstDerivative u j y) := MemLp.coeFn_toLp _
  refine ⟨ν, hν, ?_⟩
  intro D
  obtain ⟨_, _, hτ⟩ := P201.NormalTrace.forEveryTrace Ω hΩ D
  obtain ⟨τ, hpair, _, huniq⟩ := hτ (hGradient u) 0 (P201.NormalTrace.gradientDivergence Ω u 0 hu)
  refine ⟨τ, hpair, huniq, ?_⟩
  intro b
  let z := D.lift b
  have htz : D.trace z = b := D.right_inverse b
  have hgb : (hGradient z : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω]
      fun y => WithLp.toLp 2 (fun j => hFirstDerivative z j y) := MemLp.coeFn_toLp _
  have hbi (i : Fin (m + 1)) := hscalar D i (v i) z
  have hboundary : Integrable (fun y => Trace.inclusion Ω hΩ b y *
      ∑ i, Trace.inclusion Ω hΩ (D.trace (v i)) y * ν y i) (boundaryMeasure Ω) := by
    have hs := integrable_finsetSum Finset.univ (fun i _ => (hbi i).1)
    rw [htz] at hs
    convert hs using 1
    funext y
    simp only [Finset.mul_sum, mul_assoc]
  refine ⟨hboundary, ?_⟩
  have hpairz := hpair z
  rw [htz] at hpairz
  have hbulk (i : Fin (m + 1)) : IntegrableOn (fun y =>
      hUnderlying Ω 1 (v i) y * hFirstDerivative z i y +
      hFirstDerivative (v i) i y * hUnderlying Ω 1 z y) Ω volume :=
    ((Lp.memLp _).integrable_mul (Lp.memLp _)).add
      ((Lp.memLp _).integrable_mul (Lp.memLp _))
  calc
    τ b = ∫ y in Ω, inner ℝ (hGradient u y) (hGradient z y) +
        (0 : Lp ℝ Ω 2) y * hUnderlying Ω 1 z y := hpairz
    _ = ∫ y in Ω, ∑ i, (hUnderlying Ω 1 (v i) y * hFirstDerivative z i y +
        hFirstDerivative (v i) i y * hUnderlying Ω 1 z y) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hv, hgu, hgb, hdiva,
        Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with y hyv hyu hyz hydiv hy0
      have hy00 : (0 : Lp ℝ Ω 2) y = 0 := hy0
      rw [hy00, zero_mul, add_zero, hyz]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hydiv, zero_mul, add_zero]
      have hinner : inner ℝ (hGradient u y)
          (WithLp.toLp 2 (fun j => hFirstDerivative z j y)) =
          ∑ i, hGradient u y i * hFirstDerivative z i y := by
        simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      rw [hinner]
      exact Finset.sum_congr rfl (fun i _ => by rw [hyv i])
    _ = ∑ i, ∫ y in Ω, (hUnderlying Ω 1 (v i) y * hFirstDerivative z i y +
        hFirstDerivative (v i) i y * hUnderlying Ω 1 z y) :=
      integral_finsetSum _ (fun i _ => hbulk i)
    _ = ∑ i, ∫ y, Trace.inclusion Ω hΩ (D.trace z) y *
        Trace.inclusion Ω hΩ (D.trace (v i)) y * ν y i ∂boundaryMeasure Ω :=
      Finset.sum_congr rfl (fun i _ => (hbi i).2)
    _ = ∫ y, ∑ i, (Trace.inclusion Ω hΩ (D.trace z) y *
        Trace.inclusion Ω hΩ (D.trace (v i)) y * ν y i) ∂boundaryMeasure Ω :=
      (integral_finsetSum _ (fun i _ => (hbi i).1)).symm
    _ = _ := by
      rw [htz]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [Finset.mul_sum, mul_assoc]

/-- An a.e. harmonic representative determines the actual zero L² Laplacian
of any H¹ class representing it. -/
lemma hasLaplacian_of_harmonic_ae {n : ℕ} (U : Domain n) (u : H ℝ U 1)
    (g : Space n → ℝ) (hg : P201Specs.MeanValues.IsHarmonic U g)
    (hu : (hUnderlying U 1 u : Space n → ℝ) =ᵐ[domainMeasure U] g) :
    HasLaplacian U u 0 := by
  have he : regularDistribution U (hUnderlying U 1 u) = regularDistribution U g :=
    (P102.U4.regular_injectivity n ℝ U _ _
      (P102.U4.domainLp_locallyIntegrable U 2 _)
      (hg.1.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)).mpr hu
  change distributionLaplacian (regularDistribution U (hUnderlying U 1 u)) = _
  rw [he, harmonic_distribution_zero U g hg]
  exact (regularLpMap U).map_zero.symm

/-- The analytic collar-to-normal-trace bridge is dimension independent. It
uses an actual H² class and an actual Lipschitz collar certificate. -/
theorem green_collar_normal_trace_of_h2 {m : ℕ} (Ω : Domain (m + 1))
    {x : Space (m + 1)} (g : Space (m + 1) → ℝ) (hg : IsGreenFunction Ω x g)
    (r : ℝ) (hr : 0 < r) (hball : closedBall x (2 * r) ⊆ (Ω : Set _))
    (hC : IsBoundedLipschitzOpen (collar Ω x r))
    (w : H ℝ (collar Ω x r) 2)
    (hw : (hUnderlying (collar Ω x r) 2 w : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure (collar Ω x r)] g) :
    HasCollarNormalTrace Ω x g := by
  let C := collar Ω x r
  obtain ⟨u, v, hu, hv⟩ := h2_h1_gradient_classes C w
  have hug : (hUnderlying C 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure C] g := by
    rw [hu]
    exact hw
  have hCV : C ≤ punctured Ω x := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    simp only [mem_singleton_iff]
    intro heq
    subst y
    exact hy.2 (mem_closedBall_self hr.le)
  have hgh : P201Specs.MeanValues.IsHarmonic C g :=
    ⟨hg.2.2.2.1.1.mono hCV, fun y hy => hg.2.2.2.1.2 y (hCV hy)⟩
  have hlap := hasLaplacian_of_harmonic_ae C u g hgh hug
  have hva (i : Fin (m + 1)) : (hUnderlying C 1 (v i) : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure C] fun y => hGradient u y i := by
    have hga : (hGradient u : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure C]
        fun y => WithLp.toLp 2 (fun j => hFirstDerivative u j y) := MemLp.coeFn_toLp _
    rw [hv i]
    filter_upwards [hga] with y hy
    exact (congrArg (fun z : Space (m + 1) => z i) hy).symm
  obtain ⟨ν, hν, htrace⟩ := harmonic_h1_gradient_normal_trace C hC u v hva hlap
  refine ⟨r, hr, hball, hC, u, w, hug, hw, hlap, ?_⟩
  intro D
  obtain ⟨τ, hpair, huniq, hflux⟩ := htrace D
  exact ⟨τ, hpair, huniq, ν, v, hν, hva, hflux⟩

/-- For the constructed higher-dimensional row, collar geometry is the only
geometric input to its complete normal-trace clause. -/
theorem green_collar_normal_trace_of_lipschitz {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    {x : Space (m + 1)} (g : Space (m + 1) → ℝ) (hg : IsGreenFunction Ω x g)
    (hcorr : HasHarmonicCorrection Ω x g) (r : ℝ) (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ (Ω : Set _))
    (hC : IsBoundedLipschitzOpen (collar Ω x r)) : HasCollarNormalTrace Ω x g := by
  obtain ⟨w, hw⟩ := green_collar_h2 Ω hb g hcorr hr
  exact green_collar_normal_trace_of_h2 Ω g hg r hr hball hC w hw

open P201Specs P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
theorem chartImage_exists_small_subset {m : ℕ} {A : Set (Ambient m)}
    (C : BoundaryChart A) {W : Set (Ambient m)}
    (hW : W ∈ 𝓝 (C.frame (graph C.graphFunction C.center))) :
    ∃ r a : ℝ, 0 < r ∧ r ≤ C.radius ∧ 0 < a ∧ a ≤ C.height ∧
      chartImage C.frame C.graphFunction C.center r a ⊆ W := by
  obtain ⟨γ, hγ, heq⟩ := C.graph_lipschitz.extend_real
  let F : P102.U4.Space m × ℝ → Ambient m :=
    fun q => C.frame (shear γ (WithLp.toLp 2 q))
  have hF : Continuous F := C.frame.continuous.comp
    ((shearHomeomorph γ hγ.continuous).continuous.comp
      (WithLp.prod_continuous_toLp 2 (P102.U4.Space m) ℝ))
  have hcent : F (C.center, 0) = C.frame (graph C.graphFunction C.center) := by
    change C.frame (WithLp.toLp 2 (C.center, γ C.center + 0)) = _
    rw [(heq (mem_ball_self C.radius_pos)).symm, add_zero]
    rfl
  have hpre : F ⁻¹' W ∈ 𝓝 (C.center, 0) := hF.continuousAt.preimage_mem_nhds (hcent ▸ hW)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨r₀, hr₀, hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨a₀, ha₀, haV⟩ := Metric.mem_nhds_iff.mp hV
  let r := min r₀ C.radius
  let a := min a₀ C.height
  have hr : 0 < r := lt_min hr₀ C.radius_pos
  have ha : 0 < a := lt_min ha₀ C.height_pos
  have hrr : r ≤ C.radius := min_le_right _ _
  have haa : a ≤ C.height := min_le_right _ _
  refine ⟨r, a, hr, hrr, ha, haa, ?_⟩
  rw [chartImage_eq_of_eqOn C.frame (heq.mono (ball_subset_ball hrr))]
  rintro z ⟨w, ⟨v, hv, rfl⟩, rfl⟩
  apply hUV
  constructor
  · exact hrU (ball_subset_ball (min_le_left _ _) hv.1)
  · apply haV
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_lt]
    exact ⟨(neg_le_neg (min_le_left _ _)).trans_lt hv.2.1,
      hv.2.2.trans_le (min_le_left _ _)⟩

theorem upperChart_inter_smaller {m : ℕ} {A : Set (Ambient m)}
    (C : BoundaryChart A) {r a : ℝ} (hr : r ≤ C.radius) (ha : a ≤ C.height)
    (hapos : 0 < a) :
    (C.frame '' (shear C.graphFunction '' upperCylinder C.center C.radius C.height)) ∩
        chartImage C.frame C.graphFunction C.center r a =
      C.frame '' (shear C.graphFunction '' upperCylinder C.center r a) := by
  have hs : Function.Injective (shear C.graphFunction) :=
    Function.LeftInverse.injective (unshear_shear C.graphFunction)
  rw [chartImage, ← image_inter C.frame.injective, ← image_inter hs]
  congr 2
  ext z
  constructor
  · rintro ⟨hbig, hsmall⟩
    exact ⟨hsmall.1, hbig.2.1, hsmall.2.2⟩
  · intro hz
    exact ⟨⟨ball_subset_ball hr hz.1, hz.2.1, hz.2.2.trans_le ha⟩,
      hz.1, (neg_neg_of_pos hapos).trans hz.2.1, hz.2.2⟩

theorem graphChart_inter_smaller {m : ℕ} {A : Set (Ambient m)}
    (C : BoundaryChart A) {r a : ℝ} (hr : r ≤ C.radius) (ha : 0 < a) :
    (C.frame '' (graph C.graphFunction '' ball C.center C.radius)) ∩
        chartImage C.frame C.graphFunction C.center r a =
      C.frame '' (graph C.graphFunction '' ball C.center r) := by
  ext z
  constructor
  · rintro ⟨⟨w, ⟨u, hu, rfl⟩, rfl⟩, v, ⟨q, hq, hqv⟩, hv⟩
    have he : graph C.graphFunction u = shear C.graphFunction q :=
      (C.frame.injective hv).symm.trans hqv.symm
    have hh : u = q.ofLp.1 := congrArg (fun z : Ambient m => z.ofLp.1) he
    exact ⟨_, ⟨u, hh ▸ hq.1, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨⟨_, ⟨u, ball_subset_ball hr hu, rfl⟩, rfl⟩, ?_⟩
    refine ⟨_, ⟨WithLp.toLp 2 (u, (0 : ℝ)), ⟨hu, ?_⟩, ?_⟩, rfl⟩
    · exact ⟨neg_neg_of_pos ha, ha⟩
    · simp [shear, graph]

theorem boundaryChart_of_eventuallyEq {m : ℕ} {A B : Set (Ambient m)}
    (C : BoundaryChart A)
    (hAB : A =ᶠ[𝓝 (C.frame (graph C.graphFunction C.center))] B) :
    ∃ D : BoundaryChart B,
      D.frame (graph D.graphFunction D.center) = C.frame (graph C.graphFunction C.center) := by
  obtain ⟨W, hWsub, hWo, hpW⟩ := _root_.mem_nhds_iff.mp hAB
  obtain ⟨r, a, hr, hrR, ha, haA, hsub⟩ := chartImage_exists_small_subset C (hWo.mem_nhds hpW)
  let U := chartImage C.frame C.graphFunction C.center r a
  have hUU : U ⊆ chartImage C.frame C.graphFunction C.center C.radius C.height :=
    chartImage_mono _ _ _ hrR haA
  have he : A ∩ W = B ∩ W := by
    ext z
    constructor
    · rintro ⟨hzA, hzW⟩
      exact ⟨(hWsub hzW).mp hzA, hzW⟩
    · rintro ⟨hzB, hzW⟩
      exact ⟨(hWsub hzW).mpr hzB, hzW⟩
  have hfront : frontier A ∩ W = frontier B ∩ W := by
    rw [← frontier_inter_open_inter hWo, he, frontier_inter_open_inter hWo]
  have hside : B ∩ U = A ∩ U := by
    ext z
    constructor
    · rintro ⟨hzB, hzU⟩
      exact ⟨(hWsub (hsub hzU)).mpr hzB, hzU⟩
    · rintro ⟨hzA, hzU⟩
      exact ⟨(hWsub (hsub hzU)).mp hzA, hzU⟩
  have hbnd : frontier B ∩ U = frontier A ∩ U := by
    ext z
    constructor
    · rintro ⟨hzB, hzU⟩
      exact ⟨((Set.ext_iff.mp hfront z).mpr ⟨hzB, hsub hzU⟩).1, hzU⟩
    · rintro ⟨hzA, hzU⟩
      exact ⟨((Set.ext_iff.mp hfront z).mp ⟨hzA, hsub hzU⟩).1, hzU⟩
  refine ⟨{ frame := C.frame
            center := C.center
            radius := r
            height := a
            radius_pos := hr
            height_pos := ha
            graphFunction := C.graphFunction
            constant := C.constant
            graph_lipschitz := C.graph_lipschitz.mono (ball_subset_ball hrR)
            side := ?_
            boundary := ?_ }, rfl⟩
  · change B ∩ U = _
    rw [hside, ← upperChart_inter_smaller C hrR haA ha, ← C.side]
    rw [inter_assoc, inter_eq_right.mpr hUU]
  · change frontier B ∩ U = _
    rw [hbnd, ← graphChart_inter_smaller C hrR ha, ← C.boundary]
    rw [inter_assoc, inter_eq_right.mpr hUU]

open P201Specs P102.U4.GraphPieces P102.Sobolev.Geometry

theorem sphere_graph_data {m : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ (ρ : ℝ) (L : NNReal), 0 < ρ ∧ ρ ≤ r / 2 ∧
      LipschitzOnWith L (fun u : P102.U4.Space m => Real.sqrt (r^2 - ‖u‖^2)) (ball 0 ρ) := by
  have hcd : ContDiffAt ℝ 1 (fun u : P102.U4.Space m => Real.sqrt (r^2 - ‖u‖^2)) 0 :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt (by simpa using (sq_pos_of_pos hr).ne')
  obtain ⟨L, U, hU, hL⟩ := hcd.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min ε (r / 2), L, lt_min hε (by positivity), min_le_right _ _, ?_⟩
  exact hL.mono ((ball_subset_ball (min_le_left _ _)).trans hεU)

theorem sphere_shear_sign {m : ℕ} {r ρ : ℝ} (hr : 0 < r) (hρ : ρ ≤ r / 2)
    (z : Ambient m) (hz : z ∈ cylinder (0 : P102.U4.Space m) ρ (r/4)) :
    (r < ‖shear (fun u : P102.U4.Space m => Real.sqrt (r^2 - ‖u‖^2)) z‖ ↔ 0 < z.ofLp.2) ∧
    (‖shear (fun u : P102.U4.Space m => Real.sqrt (r^2 - ‖u‖^2)) z‖ = r ↔ z.ofLp.2 = 0) := by
  let a : ℝ := ‖z.ofLp.1‖
  let g : ℝ := Real.sqrt (r^2 - a^2)
  let t : ℝ := z.ofLp.2
  let N : ℝ := ‖shear (fun u : P102.U4.Space m => Real.sqrt (r^2 - ‖u‖^2)) z‖
  have ha : 0 ≤ a := norm_nonneg _
  have har : a < r/2 := (show a < ρ by simpa [a, dist_zero_right] using hz.1).trans_le hρ
  have ht : -r/4 < t ∧ t < r/4 := by simpa [t, neg_div] using hz.2
  have harg : 0 ≤ r^2-a^2 := by nlinarith
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hgsq : g^2 = r^2-a^2 := Real.sq_sqrt harg
  have hgl : r/2 < g := by nlinarith
  have hN : N^2 = a^2 + (g+t)^2 := by
    dsimp [N, shear, a, g, t]
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖z.ofLp.1‖^2 + |Real.sqrt (r^2 - ‖z.ofLp.1‖^2) + z.ofLp.2|^2 = _
    rw [sq_abs]
    rfl
  have hN0 : 0 ≤ N := norm_nonneg _
  have hfactor : 0 < 2*g+t := by linarith
  change (r < N ↔ 0 < t) ∧ (N = r ↔ t = 0)
  constructor
  · constructor
    · intro h
      by_contra hle
      have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hle) hfactor.le
      nlinarith
    · intro h
      have hm := mul_pos h hfactor
      nlinarith
  · constructor
    · intro h
      have hm : t * (2*g+t) = 0 := by nlinarith
      exact (mul_eq_zero.mp hm).resolve_right hfactor.ne'
    · intro h
      nlinarith

theorem sphere_complement_chart {m : ℕ} (x p : Ambient m) {r : ℝ}
    (hr : 0 < r) (hp : p ∈ sphere x r) :
    ∃ C : BoundaryChart ((closedBall x r)ᶜ : Set (Ambient m)),
      C.frame (graph C.graphFunction C.center) = p := by
  let v : Ambient m := WithLp.toLp 2 (0, r)
  have hv : ‖v‖ = r := by simp [v, WithLp.norm_toLp_snd, abs_of_pos hr]
  have hpN : ‖p-x‖ = r := by simpa [dist_eq_norm] using mem_sphere.mp hp
  let R : Ambient m ≃ₗᵢ[ℝ] Ambient m := (ℝ ∙ (v-(p-x)))ᗮ.reflection
  have hRv : R v = p-x := Submodule.reflection_sub (hv.trans hpN.symm)
  let e : Ambient m ≃ᵃⁱ[ℝ] Ambient m := R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ (Ambient m) x)
  have he0 : e 0 = x := by simp [e]
  have hed (w : Ambient m) : dist (e w) x = ‖w‖ := by
    rw [← he0, e.dist_map, dist_zero_right]
  obtain ⟨ρ, L, hρ, hρr, hLip⟩ := sphere_graph_data (m:=m) hr
  let γ := fun u : P102.U4.Space m => Real.sqrt (r^2 - ‖u‖^2)
  let C : BoundaryChart ((closedBall x r)ᶜ : Set (Ambient m)) := {
    frame := e
    center := 0
    radius := ρ
    height := r/4
    radius_pos := hρ
    height_pos := by positivity
    graphFunction := γ
    constant := L
    graph_lipschitz := hLip
    side := by
      ext y
      constructor
      · rintro ⟨hy, w, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨_, ⟨z, ⟨hz.1, ?_⟩, rfl⟩, rfl⟩
        refine ⟨?_, hz.2.2⟩
        exact (sphere_shear_sign hr hρr z hz).1.mp (by simpa only [mem_compl_iff, mem_closedBall, hed, not_le] using hy)
      · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
        have hzC : z ∈ cylinder (0 : P102.U4.Space m) ρ (r/4) :=
          ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
        refine ⟨?_, _, ⟨z, hzC, rfl⟩, rfl⟩
        change ¬dist (e (shear γ z)) x ≤ r
        rw [hed]
        exact not_le_of_gt ((sphere_shear_sign hr hρr z hzC).1.mpr hz.2.1)
    boundary := by
      rw [frontier_compl, frontier_closedBall x hr.ne']
      ext y
      constructor
      · rintro ⟨hy, w, ⟨z, hz, rfl⟩, rfl⟩
        have hzt : z.ofLp.2 = 0 := (sphere_shear_sign hr hρr z hz).2.mp (by
          simpa only [mem_sphere, hed] using hy)
        refine ⟨_, ⟨z.ofLp.1, hz.1, ?_⟩, rfl⟩
        apply (WithLp.ofLp_injective 2)
        apply Prod.ext
        · rfl
        · change γ z.ofLp.1 = γ z.ofLp.1 + z.ofLp.2
          rw [hzt, add_zero]
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        have hz : (WithLp.toLp 2 (u, (0:ℝ)) : Ambient m) ∈ cylinder (0 : P102.U4.Space m) ρ (r/4) :=
          ⟨hu, by constructor <;> dsimp <;> linarith⟩
        have hshear : shear γ (WithLp.toLp 2 (u, (0:ℝ))) = graph γ u := by
          simp only [shear, graph, add_zero]
        refine ⟨?_, _, ⟨_, hz, hshear⟩, rfl⟩
        change dist (e (graph γ u)) x = r
        rw [hed, ← hshear]
        exact (sphere_shear_sign hr hρr _ hz).2.mpr rfl
  }
  refine ⟨C, ?_⟩
  have hγ0 : γ 0 = r := by simp [γ, Real.sqrt_sq hr.le]
  have hgv : graph γ 0 = v := by simp [graph, hγ0, v]
  change e (graph γ 0) = p
  rw [hgv]
  change x + R v = p
  rw [hRv]
  abel
lemma bounded_c2_lipschitz {m : ℕ} (Ω : Domain (m+1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m+1)))) (hC : HasCkBoundary Ω 2) :
    IsBoundedLipschitzOpen Ω := by
  let e := graphFrame m
  refine ⟨(P102.Sobolev.Extension.geometricOpen e Ω).isOpen, ?_, ?_⟩
  · have h := e.symm.lipschitzWith.isBounded_image hb
    change Bornology.IsBounded (e ⁻¹' (Ω : Set _))
    change Bornology.IsBounded (e.toEquiv.symm '' (Ω : Set _)) at h
    rwa [e.toEquiv.image_symm_eq_preimage] at h
  · intro p hp
    obtain ⟨C,hCp,_⟩ := hC p hp
    exact ⟨C,hCp⟩

lemma cutoff_fundamental_boundary {n : ℕ} (Ω : Domain n) (x : Space n)
    (β : ContDiffBump x) (hβΩ : tsupport β ⊆ (Ω : Set _)) :
    ∀ t ∈ frontier (Ω : Set _),
      (1-β t)*fundamentalKernel n (t-x) = fundamentalKernel n (t-x) := by
  intro t ht
  have htΩ : t ∉ Ω := fun h =>
    Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr Ω.isOpen) ht h
  have htβ : t ∉ tsupport β := fun h => htΩ (hβΩ h)
  simp [image_eq_zero_of_notMem_tsupport htβ]

/-- The weak data of any specified continuous harmonic extension, with
exact identification to that extension rather than a newly chosen function. -/
theorem prescribed_harmonic_weak_data_conditional
    (harmonic_lift : SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (hm : 1 ≤ m) (Ω : Domain (m+1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m+1)))) (hC : HasCkBoundary Ω 2)
    (F h : Space (m+1) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hh : MeanValues.IsHarmonic Ω h) (hc : ContinuousOn h (closure (Ω : Set _)))
    (hbound : ∀ t ∈ frontier (Ω : Set _), h t=F t) :
    ∃ (u F₁ : H ℝ Ω 1) (z : H10 ℝ Ω),
      (hUnderlying Ω 1 u : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω] h ∧
      (hUnderlying Ω 1 F₁ : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω] F ∧
      u=F₁+z.val ∧ SmoothHarmonicLift.WeakHarmonic Ω u := by
  let g : C(frontier (Ω : Set (Space (m+1))),ℝ) :=
    ⟨fun t=>F t,hF.continuous.comp continuous_subtype_val⟩
  obtain ⟨k,_,huniq,hsmooth⟩ := harmonic_lift hm Ω hb hC g
  have hext : ContinuousHarmonicLift.IsExtension Ω g h :=
    ⟨hh,hc,fun t=>hbound t t.property⟩
  have heq := huniq h hext
  obtain ⟨u,⟨⟨z,hz⟩,huweak⟩,huk,_,_⟩ := hsmooth F
    ⟨univ,isOpen_univ,subset_univ _,hF.contDiffOn⟩ (fun _=>rfl)
  refine ⟨u,u-z.val,z,?_,?_,(sub_add_cancel _ _).symm,huweak⟩
  · filter_upwards [huk,ae_restrict_mem Ω.isOpen.measurableSet] with t ht htΩ
    exact ht.trans (heq (subset_closure htΩ)).symm
  · rw [map_sub]
    filter_upwards [Lp.coeFn_sub (hUnderlying Ω 1 u) (hUnderlying Ω 1 z.val),hz] with t ht ht'
    rw [ht]
    change hUnderlying Ω 1 u t - hZeroUnderlying Ω z t = F t
    rw [ht']
    exact add_sub_cancel_right _ _

/-- Realize the actual classical Laplacian of a smooth H¹ representative
and use the already proved distributional derivative bridge. -/
lemma smooth_classical_laplacian {m : ℕ} (Ω : Domain (m+1))
    (hΩ : IsBoundedLipschitzOpen Ω) (F : Space (m+1) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (u : H ℝ Ω 1)
    (hu : (hUnderlying Ω 1 u : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω] F) :
    ∃ q : Lp ℝ Ω 2,
      (q : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω] laplacian F ∧
      NormalTrace.HasLaplacian Ω u q := by
  have hqCont : Continuous (laplacian F) := by
    have hc := P201.MeanValues.laplacian_continuousOn (⊤ : Domain (m+1)) F
      (hF.of_le (by simp)).contDiffOn
    exact continuousOn_univ.mp hc
  have hm := P201.NormalTrace.continuousOn_closure_memLp Ω hΩ (laplacian F) hqCont.continuousOn
  refine ⟨hm.toLp _,hm.coeFn_toLp,?_⟩
  have hFu : regularDistribution Ω (hUnderlying Ω 1 u) = regularDistribution Ω F :=
    (P102.U4.regular_injectivity (m+1) ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _)
      (hF.continuous.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)).mpr hu
  change distributionLaplacian (regularDistribution Ω (hUnderlying Ω 1 u)) = _
  rw [hFu]
  calc
    distributionLaplacian (regularDistribution Ω F) = regularDistribution Ω (laplacian F) :=
      classical_laplacian_distribution Ω F (hF.of_le (by simp)).contDiffOn
    _ = regularDistribution Ω (hm.toLp _) := by
      apply (P102.U4.regular_injectivity (m+1) ℝ Ω _ _
        (hqCont.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
        (P102.U4.domainLp_locallyIntegrable Ω 2 _)).mpr
      exact hm.coeFn_toLp.symm

lemma exists_disjoint_pole_cutoffs {n : ℕ} (Ω : Domain n)
    {x y : Space n} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ (βx ηx : ContDiffBump x) (βy ηy : ContDiffBump y),
      βx.rOut < ηx.rIn ∧ βy.rOut < ηy.rIn ∧
      tsupport ηx ⊆ (P201Specs.GreenConstruction.punctured Ω y : Set _) ∧
      tsupport ηy ⊆ (P201Specs.GreenConstruction.punctured Ω x : Set _) ∧
      (∀ t ∈ closedBall x βx.rOut, βy t=0) ∧
      (∀ t ∈ closedBall y βy.rOut, βx t=0) := by
  obtain ⟨rx,hrx,hballx⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  obtain ⟨ry,hry,hbally⟩ := Metric.isOpen_iff.mp Ω.isOpen y hy
  let d := dist x y
  have hd : 0<d := dist_pos.mpr hxy
  let a := min (min rx ry) d
  have ha : 0<a := lt_min (lt_min hrx hry) hd
  have harx : a≤rx := (min_le_left _ _).trans (min_le_left _ _)
  have hary : a≤ry := (min_le_left _ _).trans (min_le_right _ _)
  have had : a≤d := min_le_right _ _
  let r := a/8
  have hr : 0<r := by dsimp [r]; positivity
  have hrrx : 3*r<rx := by dsimp [r]; linarith
  have hrry : 3*r<ry := by dsimp [r]; linarith
  have hrd : 3*r<d := by dsimp [r]; linarith
  have hrd2 : 2*r<d := by linarith
  let βx : ContDiffBump x := ⟨r/2,r,by positivity,by linarith⟩
  let ηx : ContDiffBump x := ⟨2*r,3*r,by positivity,by linarith⟩
  let βy : ContDiffBump y := ⟨r/2,r,by positivity,by linarith⟩
  let ηy : ContDiffBump y := ⟨2*r,3*r,by positivity,by linarith⟩
  refine ⟨βx,ηx,βy,ηy,by dsimp [βx,ηx]; linarith,
    by dsimp [βy,ηy]; linarith,?_,?_,?_,?_⟩
  · intro t ht
    rw [ηx.tsupport_eq] at ht
    have ht' : dist t x ≤ 3*r := ht
    refine ⟨hballx (lt_of_le_of_lt ht' hrrx),?_⟩
    have hty : t≠y := by
      intro he; subst t
      exact (not_lt_of_ge ht') (by simpa only [dist_comm] using hrd)
    simpa using hty
  · intro t ht
    rw [ηy.tsupport_eq] at ht
    have ht' : dist t y ≤ 3*r := ht
    refine ⟨hbally (lt_of_le_of_lt ht' hrry),?_⟩
    have htx : t≠x := by
      intro he; subst t
      exact (not_lt_of_ge ht') hrd
    simpa using htx
  · intro t ht
    apply βy.zero_of_le_dist
    have ht' : dist t x≤r := ht
    have htri := dist_triangle x t y
    rw [dist_comm x t] at htri
    change r≤dist t y
    dsimp [d] at hrd2
    linarith
  · intro t ht
    apply βx.zero_of_le_dist
    have ht' : dist t y≤r := ht
    have htri := dist_triangle y t x
    rw [dist_comm y t,dist_comm y x] at htri
    change r≤dist t x
    dsimp [d] at hrd2
    linarith

lemma cutoff_laplacian_zero {n : ℕ} (hn : 1 ≤ n) (x : Space n)
    (β : ContDiffBump x) {t : Space n} (ht : t ∉ closedBall x β.rOut) :
    laplacian (fun z => (1-β z)*fundamentalKernel n (z-x)) t=0 := by
  have htβ : t ∉ tsupport β := by simpa only [β.tsupport_eq] using ht
  have hlocal : (fun z => (1-β z)*fundamentalKernel n (z-x)) =ᶠ[𝓝 t]
      (fun z => fundamentalKernel n (z-x)) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp htβ] with z hz
    simp [hz]
  have htx : t ≠ x := by
    intro he; subst t
    exact ht (mem_closedBall_self β.rOut_pos.le)
  exact (P201.Weyl.laplacian_eq_of_eventuallyEq hlocal).trans
    ((translated_fundamental_harmonic hn (⊤ : Domain n) x).2 t
      ⟨mem_univ _,by simpa using htx⟩)

/-- The energy interaction of one smooth fundamental cutoff and the weak
zero-boundary correction at the other pole is the negative Green value. -/
theorem cutoff_energy_green_value {m : ℕ} (Ω : Domain (m+1))
    (hΩ : IsBoundedLipschitzOpen Ω) (x y : Space (m+1))
    (βx ηx : ContDiffBump x) (βy : ContDiffBump y)
    (hβη : βx.rOut < ηx.rIn)
    (hη : tsupport ηx ⊆ (P201Specs.GreenConstruction.punctured Ω y : Set _))
    (hcross : ∀ t ∈ closedBall x βx.rOut, βy t=0)
    (Gy h : Space (m+1) → ℝ) (hGy : P201Specs.GreenConstruction.IsGreenFunction Ω y Gy)
    (hformula : ∀ t ∈ closure (Ω : Set _) \ {y},
      Gy t=fundamentalKernel (m+1) (t-y)-h t)
    (Fx : H ℝ Ω 1) (zy : H10 ℝ Ω)
    (hFx : (hUnderlying Ω 1 Fx : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω]
      (fun t => (1-βx t)*fundamentalKernel (m+1) (t-x)))
    (hzy : (hZeroUnderlying Ω zy : Space (m+1) → ℝ) =ᵐ[domainMeasure Ω]
      (fun t=>h t-(1-βy t)*fundamentalKernel (m+1) (t-y))) :
    ellipticEnergyForm Ω (fun _=>(1 : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)) Fx zy.val = -Gy x := by
  let F := fun t => (1-βx t)*fundamentalKernel (m+1) (t-x)
  have hn : 1≤m+1 := Nat.succ_le_succ (Nat.zero_le m)
  have hFs := cutoff_fundamental_smooth x βx
  obtain ⟨q,hq,hqΔ⟩ := smooth_classical_laplacian Ω hΩ F hFs Fx hFx
  have hball : closedBall x βx.rOut ⊆ tsupport ηx := by
    rw [ηx.tsupport_eq]
    exact closedBall_subset_closedBall (hβη.trans ηx.rIn_lt_rOut).le
  have hqprod : (∫ t in Ω, q t*hZeroUnderlying Ω zy t) =
      -∫ t in Ω, laplacian F t*Gy t := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hq,hzy,ae_restrict_mem Ω.isOpen.measurableSet] with t ht ht' htΩ
    rw [ht,ht']
    by_cases htb : t ∈ closedBall x βx.rOut
    · have hty : t ∈ P201Specs.GreenConstruction.punctured Ω y := hη (hball htb)
      have hf := hformula t ⟨subset_closure htΩ,hty.2⟩
      rw [hcross t htb,sub_zero,one_mul]
      rw [hf]
      ring
    · have hzero : laplacian F t=0 := cutoff_laplacian_zero hn x βx htb
      rw [hzero]
      ring
  have hqwhole : (∫ t in Ω, laplacian F t*Gy t) = ∫ t, laplacian F t*Gy t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t htΩ
    have htb : t ∉ closedBall x βx.rOut := fun htb => htΩ (hη (hball htb)).1
    rw [cutoff_laplacian_zero hn x βx htb,zero_mul]
  have hev := cutoff_fundamental_evaluation hn Ω (P201Specs.GreenConstruction.punctured Ω y)
    x βx ηx hβη (fun t ht=>(hη ht).1) hη Gy hGy.2.2.1 hGy.2.2.2.1
  calc
    ellipticEnergyForm Ω (fun _=>(1 : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)) Fx zy.val =
        -∫ t in Ω,q t*hZeroUnderlying Ω zy t := energy_laplacian_zero hn Ω Fx q hqΔ zy
    _ = ∫ t in Ω,laplacian F t*Gy t := by rw [hqprod,neg_neg]
    _ = ∫ t,laplacian F t*Gy t := hqwhole
    _ = -Gy x := hev

lemma zero_correction_representative {n : ℕ} (Ω : Domain n)
    (u F₁ : H ℝ Ω 1) (z : H10 ℝ Ω) (h F : Space n → ℝ)
    (hu : (hUnderlying Ω 1 u : Space n → ℝ) =ᵐ[domainMeasure Ω] h)
    (hF : (hUnderlying Ω 1 F₁ : Space n → ℝ) =ᵐ[domainMeasure Ω] F)
    (heq : u=F₁+z.val) :
    (hZeroUnderlying Ω z : Space n → ℝ) =ᵐ[domainMeasure Ω] fun t=>h t-F t := by
  rw [heq,map_add] at hu
  filter_upwards [hu,hF,Lp.coeFn_add (hUnderlying Ω 1 F₁) (hUnderlying Ω 1 z.val)]
    with t hut hFt hadd
  change hUnderlying Ω 1 z.val t = _
  have h := hadd.symm.trans hut
  change hUnderlying Ω 1 F₁ t + hUnderlying Ω 1 z.val t = _ at h
  rw [hFt] at h
  exact eq_sub_of_add_eq' h

/-- Reciprocity for any two Green rows with their actual harmonic
corrections, derived from weak energy symmetry and normalized compact tests. -/
theorem green_symmetry_conditional
    (harmonic_lift : SmoothHarmonicLift.HarmonicLiftStatement)
    {m : ℕ} (hm : 1≤m) (Ω : Domain (m+1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m+1)))) (hC : HasCkBoundary Ω 2)
    {x y : Space (m+1)} (hx : x∈Ω) (hy : y∈Ω) (hxy : x≠y)
    (Gx Gy : Space (m+1) → ℝ)
    (hGx : P201Specs.GreenConstruction.IsGreenFunction Ω x Gx)
    (hGy : P201Specs.GreenConstruction.IsGreenFunction Ω y Gy)
    (hcx : P201Specs.GreenConstruction.HasHarmonicCorrection Ω x Gx)
    (hcy : P201Specs.GreenConstruction.HasHarmonicCorrection Ω y Gy) :
    Gx y = Gy x := by
  obtain ⟨βx,ηx,βy,ηy,hβηx,hβηy,hηx,hηy,hcrossx,hcrossy⟩ :=
    exists_disjoint_pole_cutoffs Ω hx hy hxy
  have hβxΩ : tsupport βx ⊆ (Ω : Set _) := by
    rw [βx.tsupport_eq]
    intro t ht
    have htη : t∈tsupport ηx := by
      rw [ηx.tsupport_eq]
      exact closedBall_subset_closedBall (hβηx.trans ηx.rIn_lt_rOut).le ht
    exact (hηx htη).1
  have hβyΩ : tsupport βy ⊆ (Ω : Set _) := by
    rw [βy.tsupport_eq]
    intro t ht
    have htη : t∈tsupport ηy := by
      rw [ηy.tsupport_eq]
      exact closedBall_subset_closedBall (hβηy.trans ηy.rIn_lt_rOut).le ht
    exact (hηy htη).1
  obtain ⟨hx₀,hhx,hcx,hbx,_,hformx⟩ := hcx
  obtain ⟨hy₀,hhy,hcy,hby,_,hformy⟩ := hcy
  let Fx := fun t => (1-βx t)*fundamentalKernel (m+1) (t-x)
  let Fy := fun t => (1-βy t)*fundamentalKernel (m+1) (t-y)
  have hbFx : ∀ t∈frontier (Ω : Set _), hx₀ t=Fx t := fun t ht=>
    (hbx t ht).trans (cutoff_fundamental_boundary Ω x βx hβxΩ t ht).symm
  have hbFy : ∀ t∈frontier (Ω : Set _), hy₀ t=Fy t := fun t ht=>
    (hby t ht).trans (cutoff_fundamental_boundary Ω y βy hβyΩ t ht).symm
  obtain ⟨ux,F₁x,zx,hux,hFx,heqx,hweakx⟩ := prescribed_harmonic_weak_data_conditional
    harmonic_lift hm Ω hb hC Fx hx₀ (cutoff_fundamental_smooth x βx) hhx hcx hbFx
  obtain ⟨uy,F₁y,zy,huy,hFy,heqy,hweaky⟩ := prescribed_harmonic_weak_data_conditional
    harmonic_lift hm Ω hb hC Fy hy₀ (cutoff_fundamental_smooth y βy) hhy hcy hbFy
  have hzx := zero_correction_representative Ω ux F₁x zx hx₀ Fx hux hFx heqx
  have hzy := zero_correction_representative Ω uy F₁y zy hy₀ Fy huy hFy heqy
  rw [heqx] at hweakx
  rw [heqy] at hweaky
  have hrec := affine_harmonic_reciprocity Ω F₁x F₁y zx zy hweakx hweaky
  have hΩ := bounded_c2_lipschitz Ω hb hC
  have hevalx := cutoff_energy_green_value Ω hΩ x y βx ηx βy hβηx hηx hcrossx
    Gy hy₀ hGy hformy F₁x zy hFx hzy
  have hevaly := cutoff_energy_green_value Ω hΩ y x βy ηy βx hβηy hηy hcrossy
    Gx hx₀ hGx hformx F₁y zx hFy hzx
  have hneg : -Gy x = -Gx y := hevalx.symm.trans (hrec.trans hevaly)
  exact neg_injective hneg.symm
theorem isLipschitzOpen_remove_closedBall {m : ℕ} {A : Set (Ambient m)}
    (hA : IsLipschitzOpen A) {x : Ambient m} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ A) : IsLipschitzOpen (A \ closedBall x r) := by
  let B := A \ closedBall x r
  refine ⟨hA.1.sdiff isClosed_closedBall, hA.2.1.subset sdiff_subset, ?_⟩
  intro p hp
  have hfr : p ∈ frontier A ∪ sphere x r := by
    have h := frontier_inter_subset A (closedBall x r)ᶜ hp
    rcases h with h | h
    · exact Or.inl h.1
    · exact Or.inr (frontier_closedBall_subset_sphere (by simpa only [frontier_compl] using h.2))
  rcases hfr with hpA | hpS
  · obtain ⟨C, hCp⟩ := hA.2.2 p hpA
    have hpout : p ∉ closedBall x r := by
      have hpnot : p ∉ A := (hA.1.frontier_eq ▸ hpA).2
      have hd : 2 * r < dist p x := lt_of_not_ge (fun h => hpnot (hball h))
      exact fun h => (by linarith : r < dist p x).not_ge h
    have hAB : A =ᶠ[𝓝 p] B := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hpout] with y hy
      exact propext ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
    obtain ⟨D, hD⟩ := boundaryChart_of_eventuallyEq (B := B) C (by simpa only [hCp] using hAB)
    exact ⟨D, hD.trans hCp⟩
  · obtain ⟨C, hCp⟩ := sphere_complement_chart x p hr hpS
    have hpA : p ∈ A := hball (by
      change dist p x ≤ 2 * r
      rw [mem_sphere.mp hpS]
      linarith)
    have hAB : ((closedBall x r)ᶜ : Set (Ambient m)) =ᶠ[𝓝 p] B := by
      filter_upwards [hA.1.mem_nhds hpA] with y hy
      exact propext ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩
    obtain ⟨D, hD⟩ := boundaryChart_of_eventuallyEq (B := B) C (by simpa only [hCp] using hAB)
    exact ⟨D, hD.trans hCp⟩

 theorem collar_isLipschitz {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasCkBoundary Ω 2) {x : Space (m + 1)} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ (Ω : Set (Space (m + 1)))) :
    IsBoundedLipschitzOpen (collar Ω x r) := by
  let e := graphFrame m
  let A := e ⁻¹' (Ω : Set (Space (m + 1)))
  have hA : IsLipschitzOpen A := by
    refine ⟨Ω.isOpen.preimage e.continuous,
      e.isometry.antilipschitzWith.isBounded_preimage hb, ?_⟩
    intro p hp
    obtain ⟨C, hC, _⟩ := hboundary p hp
    exact ⟨C, hC⟩
  have hballA : closedBall (e.symm x) (2 * r) ⊆ A := by
    intro y hy
    apply hball
    change dist (e y) x ≤ 2 * r
    rw [← e.apply_symm_apply x, e.dist_map]
    exact hy
  change IsLipschitzOpen (e ⁻¹' ((Ω : Set (Space (m + 1))) \ closedBall x r))
  rw [preimage_sdiff, e.preimage_closedBall]
  exact isLipschitzOpen_remove_closedBall hA hr hballA
/-- Conditional derivation of the complete original construction theorem.
The only explicit premise is the full frozen harmonic-lifting statement;
the closed original theorem is reserved for dependency closure by the owner. -/
theorem construction_conditional
    (harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement) :
    P201Specs.GreenConstruction.ConstructionStatement := by
  intro m Ω hb hboundary
  cases m with
  | zero =>
    obtain ⟨G, hG, hsym, hpos, hzero, hinterval⟩ :=
      construction_one_without_collar Ω hb
    refine ⟨G, ?_, hsym, hpos, hzero, by omega, hinterval⟩
    intro x hx
    refine ⟨(hG x hx).1, (hG x hx).2, ?_⟩
    obtain ⟨r, hr, hball⟩ := exists_collar_radius Ω hx
    have hC := collar_isLipschitz Ω hb hboundary hr hball
    have hCV : collar Ω x r ≤ punctured Ω x := by
      intro y hy
      refine ⟨hy.1, ?_⟩
      simp only [mem_singleton_iff]
      intro heq
      subst y
      exact hy.2 (mem_closedBall_self hr.le)
    obtain ⟨w, hw⟩ := interval_formula_hilbert_representative Ω (collar Ω x r)
      (hb.subset (fun _ hy => hy.1)) hx (hinterval x hx) hCV 2 le_rfl
    exact green_collar_normal_trace_of_h2 Ω (G x) (hG x hx).1 r hr hball hC w hw
  | succ k =>
    have hm : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    obtain ⟨G, hG, _, hpos, hzero⟩ :=
      green_kernel_signs_conditional harmonic_lift hm Ω hb hboundary
    refine ⟨G, ?_, ?_, hpos, hzero, fun _ x hx => (hG x hx).2.2, trivial⟩
    · intro x hx
      refine ⟨(hG x hx).1, (hG x hx).2.1, ?_⟩
      obtain ⟨r, hr, hball⟩ := exists_collar_radius Ω hx
      exact green_collar_normal_trace_of_lipschitz Ω hb (G x) (hG x hx).1
        (hG x hx).2.2 r hr hball (collar_isLipschitz Ω hb hboundary hr hball)
    · intro x hx y hy hxy
      exact green_symmetry_conditional harmonic_lift hm Ω hb hboundary hx hy hxy
        (G x) (G y) (hG x hx).1 (hG y hy).1 (hG x hx).2.2 (hG y hy).2.2

end P201.GreenConstruction

theorem _root_.«P201».«GreenConstruction».«construction» : _root_.«P201Specs».«GreenConstruction».«ConstructionStatement» :=
  @_root_.«P201».«GreenConstruction».«construction_conditional» (@_root_.«P201».«SmoothHarmonicLift».«harmonic_lift»)
