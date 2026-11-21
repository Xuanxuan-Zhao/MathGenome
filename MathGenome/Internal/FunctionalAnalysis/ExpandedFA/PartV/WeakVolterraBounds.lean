import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeakVolterraBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.BetaSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.SchurLp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The unnormalized weakly singular Volterra theorem.
The Gamma-series estimates below do not impose a smallness assumption.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ExpandedFA.PartV.WeakVolterraBounds

open ExpandedFA.PartV.FractionalIntegrals.Spec

/-- The convention at the endpoint is the ordinary integral over the empty set. -/
theorem weak_zero_time : Spec.ZeroTime := by
  intro 𝕜 _ T α k f
  simp [Spec.weakValue]

/-- Changing a representative preserves both absolute existence and the value
of every integral on the original interval. -/
theorem representative_independence : Spec.RepresentativeIndependence := by
  intro 𝕜 _ T α k f g hfg t ht
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have he : Spec.weakIntegrand α k f t =ᵐ[volume.restrict (Ioc 0 t)]
      Spec.weakIntegrand α k g t := by
    have h := ae_restrict_of_ae_restrict_of_subset hsub hfg
    filter_upwards [h] with s hs
    simp only [Spec.weakIntegrand, hs]
  exact ⟨integrable_congr he, integral_congr_ae he⟩

/-- A constant amplitude gives the existing power integral, without a Gamma
normalization. This is an identity of the actual integrands on the triangle. -/
theorem constant_amplitude : Spec.ConstantAmplitude := by
  intro 𝕜 _ T α c f t ht
  rw [Spec.weakValue, powerValue, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  have hmem : (t,s) ∈ Spec.triangle T := ⟨hs.1.le, hs.2, ht.2⟩
  simp only [Spec.weakIntegrand, Spec.amplitudeValue, dite_eq_left hmem,
    ContinuousMap.const_apply]
  exact (mul_smul_comm ((t-s) ^ (α-1)) c (f s)).symm

/-- Restrict Euler's integral to a fixed interval of length one. -/
lemma gamma_lower_bound {x R : ℝ} (hx : 0 ≤ x) (hR : 0 < R) :
    Real.exp (-(R + 1)) * R ^ x ≤ Real.Gamma (x + 1) := by
  have hi := Real.GammaIntegral_convergent (by linarith : 0 < x + 1)
  have hsub : Icc R (R + 1) ⊆ Ioi (0 : ℝ) := fun t ht => hR.trans_le ht.1
  have hir := hi.mono_set hsub
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (-(R + 1)) * R ^ x)
      (Icc R (R + 1)) := integrableOn_const (by simp)
  have hle : (∫ t in Icc R (R + 1), Real.exp (-(R + 1)) * R ^ x) ≤
      ∫ t in Icc R (R + 1), Real.exp (-t) * t ^ ((x + 1) - 1) := by
    apply setIntegral_mono_on hc hir measurableSet_Icc
    intro t ht
    simp only [add_sub_cancel_right]
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [ht.2]))
      (Real.rpow_le_rpow hR.le ht.1 hx) (Real.rpow_nonneg hR.le _) (Real.exp_pos _).le
  have hle' : (∫ t in Icc R (R + 1), Real.exp (-t) * t ^ ((x + 1) - 1)) ≤
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ ((x + 1) - 1) := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
    · exact Eventually.of_forall hsub
  rw [← Real.Gamma_eq_integral (by linarith : 0 < x + 1)] at hle'
  have hconst : (∫ t in Icc R (R + 1), Real.exp (-(R + 1)) * R ^ x) =
      Real.exp (-(R + 1)) * R ^ x := by simp
  exact hconst ▸ hle.trans hle'

/-- Every geometric numerator is dominated by the Gamma denominator. -/
theorem summable_pow_div_gamma {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c) :
    Summable (fun n : ℕ => c ^ n / Real.Gamma ((n : ℝ) * α + 1)) := by
  obtain ⟨R₀, hR₀⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hα)) (c + 1)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRc : c < R ^ α := lt_of_lt_of_le (by linarith : c < c + 1) (hR₀ R (le_max_left _ _))
  have hq : c / R ^ α < 1 := (div_lt_one (Real.rpow_pos_of_pos hR _)).mpr hRc
  have hs := (summable_geometric_of_lt_one
    (div_nonneg hc (Real.rpow_nonneg hR.le α)) hq).mul_left (Real.exp (R + 1))
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (pow_nonneg hc _) (Real.Gamma_pos_of_pos (by positivity)).le)
    (fun n => ?_) hs
  have hg := gamma_lower_bound (mul_nonneg (Nat.cast_nonneg n) hα.le) hR
  have hgpos : 0 < Real.exp (-(R + 1)) * R ^ ((n : ℝ) * α) := by positivity
  calc
    c ^ n / Real.Gamma ((n : ℝ) * α + 1) ≤
        c ^ n / (Real.exp (-(R + 1)) * R ^ ((n : ℝ) * α)) :=
      div_le_div_of_nonneg_left (pow_nonneg hc _) hgpos hg
    _ = Real.exp (R + 1) * (c / R ^ α) ^ n := by
      rw [mul_comm (n : ℝ) α, Real.rpow_mul_natCast hR.le, div_pow, Real.exp_neg]
      field_simp

theorem gamma_summability : Spec.GammaSummability := summable_pow_div_gamma

/-- All exponential rescalings of the power norms are summable. -/
lemma summable_norm_pow_div {A : Type*} [NormedRing A]
    {α T M : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M) (V : A)
    (hV : ∀ n : ℕ, ‖V ^ n‖ ≤ Spec.iterateBound α T M n)
    {r : ℝ} (hr : 0 < r) : Summable (fun n : ℕ => ‖V ^ n‖ / r ^ n) := by
  have hs := summable_pow_div_gamma hα
    (show 0 ≤ M * Real.Gamma α * T ^ α / r by positivity)
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  calc
    ‖V ^ n‖ / r ^ n ≤ Spec.iterateBound α T M n / r ^ n :=
      div_le_div_of_nonneg_right (hV n) (pow_nonneg hr.le n)
    _ = (M * Real.Gamma α * T ^ α / r) ^ n / Real.Gamma ((n : ℝ)*α+1) := by
      simp only [Spec.iterateBound, div_pow, mul_pow]
      rw [mul_comm (n : ℝ) α, Real.rpow_mul_natCast hT]
      ring

/-- The precise norm-root formulation of quasinilpotence. -/
theorem quasinilpotence_of_iterate_bound : Spec.QuasinilpotenceFromBound := by
  intro A _ α T M hα hT hM V hV
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun n => hb.trans_le (Real.rpow_nonneg (norm_nonneg _) _)
  · intro ε hε
    have he := (summable_norm_pow_div hα hT hM V hV (half_pos hε)).tendsto_atTop_zero
    have he' := he.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [he', eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hp : ‖V ^ n‖ < (ε / 2) ^ n := (div_lt_one (pow_pos (half_pos hε) n)).mp hn
    calc
      ‖V ^ n‖ ^ (1 / (n : ℝ)) ≤ ((ε / 2) ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (norm_nonneg _) hp.le (by positivity)
      _ = ε / 2 := by
        simpa only [one_div] using Real.pow_rpow_inv_natCast (half_pos hε).le (Nat.ne_of_gt hn0)
      _ < ε := half_lt_self hε

/-- The entire Neumann series is summable in the Banach algebra. -/
lemma summable_smul_pow_of_bound {𝕜 : Type*} [RCLike 𝕜]
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    {α T M : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M) (V : A)
    (hV : ∀ n : ℕ, ‖V ^ n‖ ≤ Spec.iterateBound α T M n) (z : 𝕜) :
    Summable (fun n : ℕ => z ^ n • V ^ n) := by
  have hs := summable_pow_div_gamma hα
    (show 0 ≤ ‖z‖ * M * Real.Gamma α * T ^ α by positivity)
  apply Summable.of_norm_bounded hs
  intro n
  rw [norm_smul, norm_pow]
  calc
    ‖z‖ ^ n * ‖V ^ n‖ ≤ ‖z‖ ^ n * Spec.iterateBound α T M n :=
      mul_le_mul_of_nonneg_left (hV n) (by positivity)
    _ = (‖z‖ * M * Real.Gamma α * T ^ α) ^ n /
        Real.Gamma ((n : ℝ) * α + 1) := by
      simp only [Spec.iterateBound, mul_pow]
      rw [mul_comm (n : ℝ) α, Real.rpow_mul_natCast hT]
      ring

/-- Multiplying the convergent series on either side gives the inverse. -/
theorem neumann_of_iterate_bound : Spec.NeumannFromBound := by
  intro 𝕜 _ A _ _ _ α T M hα hT hM V hV z
  have hs := summable_smul_pow_of_bound hα hT hM V hV z
  have hs' : Summable (fun n : ℕ => (z • V) ^ n) := by simpa only [smul_pow] using hs
  have hl := hs'.one_sub_mul_tsum_pow
  have hr := hs'.tsum_pow_mul_one_sub
  simp only [smul_pow] at hl hr
  exact ⟨hs, hl, hr, ⟨⟨1 - z • V, ∑' n : ℕ, z ^ n • V ^ n, hl, hr⟩, rfl⟩⟩

/-- Entire invertibility excludes every nonzero spectral value, over either
scalar field. This also handles a zero Banach algebra. -/
theorem spectral_radius_of_iterate_bound : Spec.SpectralRadiusFromBound := by
  intro 𝕜 _ A _ _ _ α T M hα hT hM V hV
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm ?_ _root_.bot_le
  refine iSup₂_le fun z hz => ?_
  have hz0 : z = 0 := by
    by_contra hz0
    have hu := (neumann_of_iterate_bound hα hT hM V hV z⁻¹).2.2.2
    have hu' : IsUnit (z • (1 - z⁻¹ • V)) :=
      IsUnit.smul (Units.mk0 z hz0) hu
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul,
      ← Algebra.algebraMap_eq_smul_one] at hu'
    exact (spectrum.mem_iff.mp hz) hu'
  simp [hz0]

/-- All the resolvent conclusions for either function-space realization follow
from its iterate estimate. The construction is a separate obligation. -/
lemma resolvent_properties_of_iterate_bound {𝕜 : Type} [RCLike 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {α T M : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (V : E →L[𝕜] E) (hV : ∀ n : ℕ, ‖V ^ n‖ ≤ Spec.iterateBound α T M n) :
    Spec.ResolventProperties V :=
  ⟨quasinilpotence_of_iterate_bound hα hT hM V hV,
    spectral_radius_of_iterate_bound hα hT hM V hV,
    neumann_of_iterate_bound hα hT hM V hV⟩


instance triangleCompactSpace (T : ℝ) : CompactSpace (Spec.triangle T) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    ((isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_const)))
  intro z hz
  exact ⟨⟨hz.1.trans hz.2.1, hz.2.2⟩, ⟨hz.1, hz.2.1.trans hz.2.2⟩⟩

/-- A continuous retraction onto the closed time triangle. -/
def triangleProjection {T : ℝ} (hT : 0 ≤ T) (z : ℝ × ℝ) : Spec.triangle T :=
  ⟨(max 0 (min T z.1), max 0 (min (max 0 (min T z.1)) z.2)),
    le_max_left _ _, max_le (le_max_left _ _) (min_le_left _ _),
    max_le hT (min_le_left _ _)⟩

lemma continuous_triangleProjection {T : ℝ} (hT : 0 ≤ T) :
    Continuous (triangleProjection hT) := by
  apply Continuous.subtype_mk
  exact (continuous_const.max (continuous_const.min continuous_fst)).prodMk
    (continuous_const.max ((continuous_const.max
      (continuous_const.min continuous_fst)).min continuous_snd))

lemma triangleProjection_eq {T : ℝ} (hT : 0 ≤ T) {t s : ℝ}
    (h : (t,s) ∈ Spec.triangle T) : (triangleProjection hT (t,s) : ℝ × ℝ) = (t,s) := by
  have ht : 0 ≤ t := h.1.trans h.2.1
  simp [triangleProjection, min_eq_right h.2.2, max_eq_right ht,
    min_eq_right h.2.1, max_eq_right h.1]

/-- A globally continuous extension used only to prove continuity of the
original triangle integral. Retraction preserves the amplitude bound. -/
def extendedAmplitude {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (k : C(Spec.triangle T, 𝕜)) (z : ℝ × ℝ) : 𝕜 := k (triangleProjection hT z)

lemma continuous_extendedAmplitude {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜)) : Continuous (extendedAmplitude hT k) :=
  k.continuous.comp (continuous_triangleProjection hT)

lemma extendedAmplitude_eq {𝕜 : Type} [RCLike 𝕜] {T t s : ℝ}
    (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜)) (h : (t,s) ∈ Spec.triangle T) :
    extendedAmplitude hT k (t,s) = Spec.amplitudeValue k t s := by
  simp only [Spec.amplitudeValue, dite_eq_left h, extendedAmplitude]
  congr 1
  exact Subtype.ext (triangleProjection_eq hT h)

lemma amplitude_norm_le {𝕜 : Type} [RCLike 𝕜] {T M : ℝ}
    (k : C(Spec.triangle T, 𝕜)) (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M) (t s : ℝ) :
    ‖Spec.amplitudeValue k t s‖ ≤ M := by
  classical
  unfold Spec.amplitudeValue
  split_ifs
  · exact hk _
  · simpa using hM

lemma weakValue_extended {𝕜 : Type} [RCLike 𝕜] {T t : ℝ}
    (hT : 0 ≤ T) (α : ℝ) (k : C(Spec.triangle T, 𝕜)) (f : ℝ → 𝕜)
    (ht : t ∈ Icc (0 : ℝ) T) :
    Spec.weakValue α k f t = ∫ s in Ioc 0 t,
      (t-s) ^ (α-1) • (extendedAmplitude hT k (t,s) * f s) := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [extendedAmplitude_eq hT k ⟨hs.1.le, hs.2, ht.2⟩]
  rfl

lemma weak_continuous_input_integrable {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (f : C(Icc (0 : ℝ) T, 𝕜)) (t : Icc (0 : ℝ) T) :
    IntegrableOn (Spec.weakIntegrand α k (continuousExtension hT f) t) (Ioc 0 (t : ℝ)) := by
  have he : EqOn (Spec.weakIntegrand α k (continuousExtension hT f) t)
      (fun s => ((t : ℝ)-s) ^ (α-1) •
        (extendedAmplitude hT k (t,s) * continuousExtension hT f s)) (Ioc 0 (t : ℝ)) := by
    intro s hs
    dsimp only
    rw [extendedAmplitude_eq hT k ⟨hs.1.le, hs.2, t.property.2⟩]
    rfl
  apply (integrableOn_congr_fun he measurableSet_Ioc).mpr
  apply (ExpandedFA.PartV.FractionalIntegrals.reflected_power_integrable hα).smul_bdd
    (‖k‖ * ‖f‖)
    ((((continuous_extendedAmplitude hT k).comp
      (continuous_const.prodMk continuous_id)).mul
      (ExpandedFA.PartV.FractionalIntegrals.continuous_extension hT f)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro s
  exact (norm_mul_le _ _).trans (mul_le_mul
    (k.norm_coe_le_norm _) (ExpandedFA.PartV.FractionalIntegrals.extension_norm_le hT f s)
    (norm_nonneg _) (norm_nonneg _))


lemma weakValue_reflect {𝕜 : Type} [RCLike 𝕜] {T t : ℝ}
    (hT : 0 ≤ T) (α : ℝ) (k : C(Spec.triangle T, 𝕜)) (f : ℝ → 𝕜)
    (ht : t ∈ Icc (0 : ℝ) T) :
    Spec.weakValue α k f t = ∫ r in Ioc 0 t,
      r ^ (α-1) • (extendedAmplitude hT k (t,t-r) * f (t-r)) := by
  rw [weakValue_extended hT α k f ht,
    ← intervalIntegral.integral_of_le ht.1, ← intervalIntegral.integral_of_le ht.1]
  have he := intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => r ^ (α-1) • (extendedAmplitude hT k (t,t-r) * f (t-r)))
    (a := (0 : ℝ)) (b := t) t
  simpa only [sub_sub_cancel, sub_self, sub_zero] using he

/-- Dominated convergence after reflection fixes the integrable singularity.
Only continuity of the amplitude on the closed triangle is used. -/
lemma continuous_weakValue {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (f : C(Icc (0 : ℝ) T, 𝕜)) :
    ContinuousOn (Spec.weakValue α k (continuousExtension hT f)) (Icc (0 : ℝ) T) := by
  let G : ℝ → ℝ → 𝕜 := fun t r =>
    extendedAmplitude hT k (t,t-r) * continuousExtension hT f (t-r)
  have hG : Continuous (fun z : ℝ × ℝ => G z.1 z.2) :=
    ((continuous_extendedAmplitude hT k).comp
      (continuous_fst.prodMk (continuous_fst.sub continuous_snd))).mul
      ((ExpandedFA.PartV.FractionalIntegrals.continuous_extension hT f).comp
        (continuous_fst.sub continuous_snd))
  have hGb (t r : ℝ) : ‖G t r‖ ≤ ‖k‖ * ‖f‖ :=
    (norm_mul_le _ _).trans (mul_le_mul (k.norm_coe_le_norm _)
      (ExpandedFA.PartV.FractionalIntegrals.extension_norm_le hT f _)
      (norm_nonneg _) (norm_nonneg _))
  let F : ℝ → ℝ → 𝕜 := fun t r => r ^ (α-1) • (if r ≤ t then G t r else 0)
  have hm (t : ℝ) : AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 T)) := by
    exact (ExpandedFA.PartV.FractionalIntegrals.power_integrable (T := T) hα).aestronglyMeasurable.smul
      (Measurable.ite (measurableSet_le measurable_id measurable_const)
        ((hG.comp (continuous_const.prodMk continuous_id)).measurable)
        measurable_const).aestronglyMeasurable
  have hb (t : ℝ) : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
      ‖F t r‖ ≤ r ^ (α-1) * (‖k‖ * ‖f‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp [F]
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.1.le _)
    split_ifs
    · exact hGb t r
    · simp only [norm_zero]; positivity
  have hc : Continuous (fun t => ∫ r in Ioc 0 T, F t r) := by
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply continuousAt_of_dominated (Eventually.of_forall hm) (Eventually.of_forall hb)
      ((ExpandedFA.PartV.FractionalIntegrals.power_integrable hα).mul_const (‖k‖ * ‖f‖))
    have hne : ∀ᵐ r ∂volume.restrict (Ioc 0 T), r ≠ t₀ :=
      ae_restrict_of_ae (volume.ae_ne t₀)
    filter_upwards [hne] with r hr
    have hec : ContinuousAt (fun t => r ^ (α-1) • G t r) t₀ :=
      continuousAt_const.smul ((hG.comp (continuous_id.prodMk continuous_const)).continuousAt)
    rcases lt_or_gt_of_ne hr with hrt | htr
    · apply hec.congr
      filter_upwards [eventually_gt_nhds hrt] with t ht
      simp [F, ht.le]
    · apply (continuousAt_const (y := (0 : 𝕜))).congr
      filter_upwards [eventually_lt_nhds htr] with t ht
      simp [F, not_le.mpr ht]
  apply hc.continuousOn.congr
  intro t ht
  rw [weakValue_reflect hT α k _ ht]
  have he : F t = (Iic t).indicator (fun r : ℝ => r ^ (α-1) • G t r) := by
    ext r
    simp only [F, indicator_apply, mem_Iic]
    split_ifs <;> simp_all
  change _ = ∫ r in Ioc 0 T, F t r
  rw [he, setIntegral_indicator measurableSet_Iic]
  have hi : Ioc (0 : ℝ) T ∩ Iic t = Ioc 0 t := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨hr, _⟩, hrt⟩; exact ⟨hr, hrt⟩
    · rintro ⟨hr, hrt⟩; exact ⟨⟨hr, hrt.trans ht.2⟩, hrt⟩
  rw [hi]

lemma weak_continuous_input_bound {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (f : C(Icc (0 : ℝ) T, 𝕜)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖Spec.weakValue α k (continuousExtension hT f) t‖ ≤ (M * T ^ α / α) * ‖f‖ := by
  have hw : IntegrableOn (fun s : ℝ => (t-s) ^ (α-1) * (M * ‖f‖)) (Ioc 0 t) :=
    (ExpandedFA.PartV.FractionalIntegrals.reflected_power_integrable hα).mul_const _
  have hb : ‖Spec.weakValue α k (continuousExtension hT f) t‖ ≤
      t ^ α / α * (M * ‖f‖) := by
    rw [← ExpandedFA.PartV.FractionalIntegrals.reflected_power_integral hα ht.1,
      ← integral_mul_const]
    apply norm_integral_le_of_norm_le hw
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Spec.weakIntegrand, norm_smul,
      Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
    exact (norm_mul_le _ _).trans (mul_le_mul (amplitude_norm_le k hM hk t s)
      (ExpandedFA.PartV.FractionalIntegrals.extension_norm_le hT f s)
      (norm_nonneg _) hM)
  calc
    _ ≤ t ^ α / α * (M * ‖f‖) := hb
    _ ≤ T ^ α / α * (M * ‖f‖) := by
      gcongr <;> first | exact ht.1 | exact ht.2
    _ = _ := by ring


/-- Construct the bounded operator using continuity of its actual integral;
this includes the zero-length interval. -/
theorem continuous_construction : Spec.ContinuousConstruction := by
  intro 𝕜 _ α T hα hT k M hM hk
  let hcont (f : C(Icc (0 : ℝ) T, 𝕜)) :
      Continuous (fun t : Icc (0 : ℝ) T => Spec.weakValue α k (continuousExtension hT f) t) :=
    (continuous_weakValue hα hT k f).comp_continuous continuous_subtype_val
      (fun t => t.property)
  let L : C(Icc (0 : ℝ) T, 𝕜) →ₗ[𝕜] C(Icc (0 : ℝ) T, 𝕜) :=
    { toFun := fun f => ⟨_, hcont f⟩
      map_add' := by
        intro f g
        ext t
        change Spec.weakValue α k (continuousExtension hT (f+g)) t =
          Spec.weakValue α k (continuousExtension hT f) t +
          Spec.weakValue α k (continuousExtension hT g) t
        simp only [Spec.weakValue, Spec.weakIntegrand, continuousExtension,
          ContinuousMap.add_apply, mul_add, smul_add]
        exact integral_add (weak_continuous_input_integrable hα hT k f t)
          (weak_continuous_input_integrable hα hT k g t)
      map_smul' := by
        intro c f
        ext t
        change Spec.weakValue α k (continuousExtension hT (c • f)) t =
          c • Spec.weakValue α k (continuousExtension hT f) t
        simp only [Spec.weakValue, Spec.weakIntegrand, continuousExtension,
          ContinuousMap.smul_apply, smul_eq_mul]
        simp_rw [← mul_assoc, mul_comm (Spec.amplitudeValue k _ _) c, mul_assoc,
          ← smul_eq_mul c, smul_comm (_ : ℝ) c]
        exact integral_smul c _ }
  have hB : 0 ≤ M * T ^ α / α := by positivity
  have hb (f) : ‖L f‖ ≤ (M * T ^ α / α) * ‖f‖ := by
    apply (ContinuousMap.norm_le (L f) (mul_nonneg hB (norm_nonneg f))).mpr
    intro t
    exact weak_continuous_input_bound hα hT k hM hk f t.property
  refine ⟨L.mkContinuous (M * T ^ α / α) hb, ?_,
    LinearMap.mkContinuous_norm_le _ hB hb⟩
  intro f t
  exact ⟨weak_continuous_input_integrable hα hT k f t, rfl⟩


/-- The positive Beta majorant controls every iterate at every output time. -/
lemma continuous_iterate_pointwise {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : ∀ f t, V f t = Spec.weakValue α k (continuousExtension hT f) t) :
    ∀ (n : ℕ) (f : C(Icc (0 : ℝ) T, 𝕜)) (t : Icc (0 : ℝ) T),
      ‖(V ^ n) f t‖ ≤ Spec.iterateBound α t M n * ‖f‖ := by
  intro n
  induction n with
  | zero =>
    intro f t
    simpa [Spec.iterateBound] using f.norm_coe_le_norm t
  | succ n ih =>
    intro f t
    have ht : 0 ≤ (t : ℝ) := t.property.1
    have hβ : 0 < (n : ℝ) * α + 1 := by positivity
    have hγ : 0 < Real.Gamma ((n : ℝ) * α + 1) := Real.Gamma_pos_of_pos hβ
    have hδ : 0 < Real.Gamma (α + ((n : ℝ) * α + 1)) :=
      Real.Gamma_pos_of_pos (add_pos hα hβ)
    rw [pow_succ', mul_apply_eq_comp, hV]
    by_cases ht0 : (t : ℝ) = 0
    · rw [ht0, weak_zero_time, norm_zero]
      exact mul_nonneg (by
        dsimp [Spec.iterateBound]
        positivity) (norm_nonneg _)
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne ht (Ne.symm ht0)
    obtain ⟨hi, hmass⟩ := ExpandedFA.PartV.BetaSemigroup.beta_convolution
      α ((n : ℝ) * α + 1) 0 t hα hβ htpos
    simp only [sub_zero, add_sub_cancel_right] at hi hmass
    let C : ℝ := M * (M ^ n * Real.Gamma α ^ n / Real.Gamma ((n : ℝ) * α + 1)) * ‖f‖
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hb : ‖Spec.weakValue α k (continuousExtension hT ((V ^ n) f)) t‖ ≤
        ∫ s in Ioc 0 (t : ℝ), ((t : ℝ)-s) ^ (α-1) * s ^ ((n : ℝ)*α) * C := by
      apply norm_integral_le_of_norm_le (hi.mul_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans t.property.2⟩
      have he : continuousExtension hT ((V ^ n) f) s = (V ^ n) f ⟨s,hsT⟩ := by
        simp only [continuousExtension, projIcc_of_mem hT hsT]
      rw [Spec.weakIntegrand, norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _), he]
      calc
        _ ≤ ((t : ℝ)-s) ^ (α-1) * (M * (Spec.iterateBound α s M n * ‖f‖)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
          exact (norm_mul_le _ _).trans (mul_le_mul
            (amplitude_norm_le k hM hk _ _) (ih f ⟨s,hsT⟩) (norm_nonneg _) hM)
        _ = _ := by dsimp [C, Spec.iterateBound]; ring
    calc
      _ ≤ ∫ s in Ioc 0 (t : ℝ), ((t : ℝ)-s) ^ (α-1) * s ^ ((n : ℝ)*α) * C := hb
      _ = (Real.Gamma α * Real.Gamma ((n : ℝ)*α+1) /
          Real.Gamma (α+((n : ℝ)*α+1))) * (t : ℝ) ^ (α+((n : ℝ)*α+1)-1) * C := by
        rw [integral_mul_const, hmass]
      _ = Spec.iterateBound α t M (n+1) * ‖f‖ := by
        have hexp : α + ((n : ℝ)*α+1)-1 = ((n+1 : ℕ) : ℝ)*α := by push_cast; ring
        have harg : α + ((n : ℝ)*α+1) = ((n+1 : ℕ) : ℝ)*α+1 := by push_cast; ring
        rw [hexp, harg]
        dsimp [C, Spec.iterateBound]
        rw [pow_succ, pow_succ]
        field_simp

lemma continuous_iterate_bound {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : ∀ f t, V f t = Spec.weakValue α k (continuousExtension hT f) t) :
    ∀ n : ℕ, ‖V ^ n‖ ≤ Spec.iterateBound α T M n := by
  intro n
  have hB : 0 ≤ Spec.iterateBound α T M n := by dsimp [Spec.iterateBound]; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro t
  apply (continuous_iterate_pointwise hα hT k hM hk V hV n f t).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  dsimp [Spec.iterateBound]
  gcongr
  · exact t.property.1
  · exact t.property.2


/-- A continuous cutoff of the power singularity, zero on negative lags. -/
def cutoffPower (α δ r : ℝ) : ℝ := (max 0 r) ^ α / max δ r

lemma continuous_cutoffPower {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    Continuous (cutoffPower α δ) := by
  apply Continuous.div
    ((continuous_const.max continuous_id).rpow_const (fun _ => Or.inr hα.le))
    (continuous_const.max continuous_id)
  intro r
  exact ne_of_gt (hδ.trans_le (le_max_left _ _))

lemma cutoffPower_zero {α δ r : ℝ} (hα : 0 < α) (hr : r ≤ 0) :
    cutoffPower α δ r = 0 := by simp [cutoffPower, max_eq_left hr, Real.zero_rpow hα.ne']

lemma cutoffPower_le {α δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    0 ≤ cutoffPower α δ r ∧ cutoffPower α δ r ≤ r ^ (α-1) := by
  dsimp [cutoffPower]
  rw [max_eq_right hr.le, Real.rpow_sub_one hr.ne']
  exact ⟨by positivity, div_le_div_of_nonneg_left (by positivity) hr (le_max_right _ _)⟩

lemma cutoffPower_eq {α δ r : ℝ} (hr : 0 < r) (hδr : δ ≤ r) :
    cutoffPower α δ r = r ^ (α-1) := by
  rw [cutoffPower, max_eq_right hr.le, max_eq_right hδr, Real.rpow_sub_one hr.ne']

lemma cutoffPower_error_integrable {α T δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    IntegrableOn (fun r => |r ^ (α-1) - cutoffPower α δ r|) (Ioc 0 T) := by
  apply (ExpandedFA.PartV.FractionalIntegrals.power_integrable hα).mono'
    (by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        ((ExpandedFA.PartV.FractionalIntegrals.power_integrable (T := T) hα).aestronglyMeasurable.sub
          (continuous_cutoffPower hα hδ).aestronglyMeasurable).norm)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg (sub_nonneg.mpr (cutoffPower_le hδ hr.1).2)]
  exact sub_le_self _ (cutoffPower_le hδ hr.1).1

lemma cutoffPower_error_tendsto {α T : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => ∫ r in Ioc 0 T,
      |r ^ (α-1) - cutoffPower α ((n+1 : ℝ)⁻¹) r|) atTop (𝓝 0) := by
  have hd (n : ℕ) : 0 < ((n+1 : ℝ)⁻¹) := by positivity
  have hδ : Tendsto (fun n : ℕ => (n+1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hlim : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
      Tendsto (fun n : ℕ => |r ^ (α-1) - cutoffPower α ((n+1 : ℝ)⁻¹) r|) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    apply tendsto_const_nhds.congr'
    filter_upwards [hδ.eventually (gt_mem_nhds hr.1)] with n hn
    simp only [cutoffPower_eq hr.1 hn.le, sub_self, abs_zero]
  have hb (n : ℕ) : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
      ‖|r ^ (α-1) - cutoffPower α ((n+1 : ℝ)⁻¹) r|‖ ≤ r ^ (α-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg (sub_nonneg.mpr (cutoffPower_le (hd n) hr.1).2)]
    exact sub_le_self _ (cutoffPower_le (hd n) hr.1).1
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun r : ℝ => r ^ (α-1))
    (fun n => (cutoffPower_error_integrable (T := T) hα (hd n)).aestronglyMeasurable)
    (ExpandedFA.PartV.FractionalIntegrals.power_integrable hα) hb hlim

instance intervalSubtypeFiniteMeasure (T : ℝ) :
    IsFiniteMeasure (volume.comap (Subtype.val : Icc (0 : ℝ) T → ℝ)) := by
  constructor
  rw [comap_subtype_coe_apply measurableSet_Icc volume Set.univ, image_univ, Subtype.range_coe]
  exact isCompact_Icc.measure_lt_top

/-- The cutoff kernel is continuous on the whole square, including its
formerly singular diagonal. -/
def cutoffKernel {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜)) :
    C(Icc (0 : ℝ) T × Icc (0 : ℝ) T, 𝕜) :=
  ⟨fun z => cutoffPower α δ ((z.1 : ℝ)-z.2) •
      extendedAmplitude hT k (z.1,z.2),
    ((continuous_cutoffPower hα hδ).comp
      ((continuous_subtype_val.comp continuous_fst).sub
        (continuous_subtype_val.comp continuous_snd))).smul
      ((continuous_extendedAmplitude hT k).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)))⟩


abbrev cutoffOperator {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜)) :=
  ExpandedFA.PartV.ContinuousKernel.kernelOperator
    (volume.comap (Subtype.val : Icc (0 : ℝ) T → ℝ)) (cutoffKernel hα hT hδ k)

lemma cutoffOperator_formula {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (f : C(Icc (0 : ℝ) T, 𝕜)) (t : Icc (0 : ℝ) T) :
    cutoffOperator hα hT hδ k f t = ∫ s in Ioc 0 (t : ℝ),
      cutoffPower α δ ((t : ℝ)-s) •
        (extendedAmplitude hT k (t,s) * continuousExtension hT f s) := by
  rw [ExpandedFA.PartV.ContinuousKernel.kernelOperator_apply]
  change (∫ s : Icc (0 : ℝ) T,
      (cutoffPower α δ ((t : ℝ)-s) • extendedAmplitude hT k (t,s)) * f s
      ∂volume.comap Subtype.val) = _
  have he : (∫ s : Icc (0 : ℝ) T,
      (cutoffPower α δ ((t : ℝ)-s) • extendedAmplitude hT k (t,s)) * f s
      ∂volume.comap Subtype.val) = ∫ s in Icc (0 : ℝ) T,
      cutoffPower α δ ((t : ℝ)-s) •
        (extendedAmplitude hT k (t,s) * continuousExtension hT f s) := by
    rw [← integral_subtype_comap measurableSet_Icc]
    congr 1
    funext s
    simp only [continuousExtension, projIcc_val, smul_mul_assoc]
  rw [he, ← restrict_Ioc_eq_restrict_Icc]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (fun s hs => ⟨hs.1, hs.2.trans t.property.2⟩)
  intro s hs
  have hts : (t : ℝ) ≤ s := le_of_not_gt (fun h => hs.2 ⟨hs.1.1, h.le⟩)
  rw [cutoffPower_zero hα (sub_nonpos.mpr hts), zero_smul]

lemma cutoffOperator_reflect {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (f : C(Icc (0 : ℝ) T, 𝕜)) (t : Icc (0 : ℝ) T) :
    cutoffOperator hα hT hδ k f t = ∫ r in Ioc 0 (t : ℝ),
      cutoffPower α δ r •
        (extendedAmplitude hT k (t,(t : ℝ)-r) * continuousExtension hT f ((t : ℝ)-r)) := by
  rw [cutoffOperator_formula hα hT hδ k f t,
    ← intervalIntegral.integral_of_le t.property.1,
    ← intervalIntegral.integral_of_le t.property.1]
  have he := intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => cutoffPower α δ r •
      (extendedAmplitude hT k (t,(t : ℝ)-r) * continuousExtension hT f ((t : ℝ)-r)))
    (a := (0 : ℝ)) (b := (t : ℝ)) t
  simpa only [sub_sub_cancel, sub_self, sub_zero] using he


lemma cutoffOperator_error_bound {𝕜 : Type} [RCLike 𝕜] {α T δ M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : ∀ f t, V f t = Spec.weakValue α k (continuousExtension hT f) t) :
    ‖V - cutoffOperator hα hT hδ k‖ ≤
      M * ∫ r in Ioc 0 T, |r ^ (α-1) - cutoffPower α δ r| := by
  let E : ℝ → ℝ := fun r => |r ^ (α-1) - cutoffPower α δ r|
  have hE : IntegrableOn E (Ioc 0 T) := cutoffPower_error_integrable hα hδ
  have hEn : ∀ r, 0 ≤ E r := fun r => abs_nonneg _
  have hB : 0 ≤ M * ∫ r in Ioc 0 T, E r := mul_nonneg hM (integral_nonneg hEn)
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro t
  let G : ℝ → 𝕜 := fun r =>
    extendedAmplitude hT k (t,(t : ℝ)-r) * continuousExtension hT f ((t : ℝ)-r)
  have hGc : Continuous G :=
    ((continuous_extendedAmplitude hT k).comp
      (continuous_const.prodMk (continuous_const.sub continuous_id))).mul
      ((ExpandedFA.PartV.FractionalIntegrals.continuous_extension hT f).comp
        (continuous_const.sub continuous_id))
  have hGb (r : ℝ) : ‖G r‖ ≤ M * ‖f‖ :=
    (norm_mul_le _ _).trans (mul_le_mul (hk _)
      (ExpandedFA.PartV.FractionalIntegrals.extension_norm_le hT f _)
      (norm_nonneg _) hM)
  have hi : IntegrableOn (fun r => r ^ (α-1) • G r) (Ioc 0 (t : ℝ)) :=
    (ExpandedFA.PartV.FractionalIntegrals.power_integrable hα).smul_bdd
      (M * ‖f‖) hGc.aestronglyMeasurable (Eventually.of_forall hGb)
  have hj : IntegrableOn (fun r => cutoffPower α δ r • G r) (Ioc 0 (t : ℝ)) :=
    ((continuous_cutoffPower hα hδ).smul hGc).integrableOn_Ioc
  have hsub : Ioc (0 : ℝ) (t : ℝ) ⊆ Ioc 0 T :=
    fun r hr => ⟨hr.1, hr.2.trans t.property.2⟩
  change ‖V f t - cutoffOperator hα hT hδ k f t‖ ≤ _
  rw [hV, weakValue_reflect hT α k _ t.property, cutoffOperator_reflect hα hT hδ k f t]
  change ‖(∫ r in Ioc 0 (t : ℝ), r ^ (α-1) • G r) -
    ∫ r in Ioc 0 (t : ℝ), cutoffPower α δ r • G r‖ ≤ _
  rw [← integral_sub hi hj]
  calc
    _ ≤ ∫ r in Ioc 0 (t : ℝ), E r * (M * ‖f‖) := by
      apply norm_integral_le_of_norm_le ((hE.mono_set hsub).mul_const _)
      apply Eventually.of_forall
      intro r
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hGb r) (hEn r)
    _ = (∫ r in Ioc 0 (t : ℝ), E r) * (M * ‖f‖) := integral_mul_const _ _
    _ ≤ (∫ r in Ioc 0 T, E r) * (M * ‖f‖) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM (norm_nonneg _))
      exact setIntegral_mono_set hE (Eventually.of_forall hEn) (Eventually.of_forall hsub)
    _ = _ := by ring

lemma continuous_isCompact {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : ∀ f t, V f t = Spec.weakValue α k (continuousExtension hT f) t) :
    IsCompactOperator V := by
  have hd (n : ℕ) : 0 < (n+1 : ℝ)⁻¹ := by positivity
  let A (n : ℕ) := cutoffOperator hα hT (hd n) k
  have hAc (n : ℕ) : IsCompactOperator (A n) :=
    ExpandedFA.PartV.ContinuousKernel.kernelOperator_isCompact _ _
  have he : Tendsto (fun n : ℕ => ‖V - A n‖) atTop (𝓝 0) := by
    apply squeeze_zero (f := fun n : ℕ => ‖V - A n‖)
      (g := fun n => M * ∫ r in Ioc 0 T, |r ^ (α-1) - cutoffPower α ((n+1 : ℝ)⁻¹) r|)
      (fun n => norm_nonneg (V - A n))
      (fun n => cutoffOperator_error_bound hα hT (hd n) k hM hk V hV)
    simpa using (cutoffPower_error_tendsto (T := T) hα).const_mul M
  apply isCompactOperator_of_tendsto (l := atTop) (F := A) ?_ (Eventually.of_forall hAc)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using he

/-- The full source conclusion on C[0,T], with its precise Gamma iterate
estimate and its two-sided Neumann inverse for every scalar parameter. -/
theorem continuous_theorem : Spec.ContinuousTheorem := by
  intro 𝕜 _ α T hα hT k M hM hk
  obtain ⟨V, hf, _⟩ := continuous_construction α T hα hT k M hM hk
  have hV : ∀ f t, V f t = Spec.weakValue α k (continuousExtension hT f) t :=
    fun f t => (hf f t).2
  have hb := continuous_iterate_bound hα hT k hM hk V hV
  exact ⟨V, hf, continuous_isCompact hα hT k hM hk V hV, hb,
    resolvent_properties_of_iterate_bound hα hT hM V hb⟩


open ExpandedFA.PartV.FractionalIntegrals
open scoped ENNReal NNReal

/-- Ambient kernel for the original weak Volterra integral. -/
def weakSchurKernel {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (α : ℝ) (k : C(Spec.triangle T, 𝕜)) (z : ℝ × ℝ) : 𝕜 :=
  powerKernel α T (z.1-z.2) • extendedAmplitude hT k z

lemma measurable_powerKernel (α T : ℝ) : Measurable (powerKernel α T) :=
  (measurable_id.pow_const _).indicator measurableSet_Ioc

lemma measurable_weakSchurKernel {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {T : ℝ} (hT : 0 ≤ T) (α : ℝ) (k : C(Spec.triangle T, 𝕜)) :
    Measurable (weakSchurKernel hT α k) :=
  ((measurable_powerKernel α T).comp (measurable_fst.sub measurable_snd)).smul
    (continuous_extendedAmplitude hT k).measurable

lemma weakSchurKernel_enorm_le {𝕜 : Type} [RCLike 𝕜] {T M : ℝ} (hT : 0 ≤ T)
    (α : ℝ) (k : C(Spec.triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M) (z : ℝ × ℝ) :
    ‖weakSchurKernel hT α k z‖ₑ ≤ ‖powerKernel α T (z.1-z.2)‖ₑ * ENNReal.ofReal M := by
  rw [weakSchurKernel, enorm_smul]
  apply mul_le_mul_right
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hk _)

/-- A real lag majorant gives equal Schur bounds on every finite interval.
No support restriction is needed because restriction decreases the integral. -/
lemma kernelBounds_of_lag_majorant {𝕜 : Type} [RCLike 𝕜]
    (T M : ℝ) (hM : 0 ≤ M) (q : ℝ × ℝ → 𝕜) (w : ℝ → ℝ)
    (hwm : Measurable w) (hwi : Integrable w volume)
    (hq : ∀ z, ‖q z‖ₑ ≤ ‖w (z.1-z.2)‖ₑ * ENNReal.ofReal M) :
    SchurLp.KernelBounds (intervalMeasure T) (intervalMeasure T) q
      ⟨M * ∫ r, ‖w r‖, mul_nonneg hM (integral_nonneg (fun _ => norm_nonneg _))⟩
      ⟨M * ∫ r, ‖w r‖, mul_nonneg hM (integral_nonneg (fun _ => norm_nonneg _))⟩ := by
  have hmass : (∫⁻ r, ‖w r‖ₑ ∂volume) = ENNReal.ofReal (∫ r, ‖w r‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm hwi).symm
  have hmeas : Measurable (fun r => ‖w r‖ₑ) := hwm.enorm
  constructor
  · apply Eventually.of_forall
    intro t
    calc
      _ ≤ ∫⁻ s, ‖w (t-s)‖ₑ * ENNReal.ofReal M ∂intervalMeasure T :=
        lintegral_mono (fun s => hq (t,s))
      _ ≤ ∫⁻ s, ‖w (t-s)‖ₑ * ENNReal.ofReal M ∂volume :=
        setLIntegral_le_lintegral _ _
      _ = (∫⁻ s, ‖w (t-s)‖ₑ ∂volume) * ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (∫ r, ‖w r‖) * ENNReal.ofReal M := by
        congr 1
        rw [(volume.measurePreserving_sub_left t).lintegral_comp hmeas, hmass]
      _ = _ := by
        rw [← ENNReal.ofReal_mul (integral_nonneg (fun _ => norm_nonneg _)), mul_comm]
        exact ENNReal.ofReal_eq_coe_nnreal _
  · apply Eventually.of_forall
    intro s
    calc
      _ ≤ ∫⁻ t, ‖w (t-s)‖ₑ * ENNReal.ofReal M ∂intervalMeasure T :=
        lintegral_mono (fun t => hq (t,s))
      _ ≤ ∫⁻ t, ‖w (t-s)‖ₑ * ENNReal.ofReal M ∂volume :=
        setLIntegral_le_lintegral _ _
      _ = (∫⁻ t, ‖w (t-s)‖ₑ ∂volume) * ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (∫ r, ‖w r‖) * ENNReal.ofReal M := by
        congr 1
        rw [(measurePreserving_sub_right volume s).lintegral_comp hmeas, hmass]
      _ = _ := by
        rw [← ENNReal.ofReal_mul (integral_nonneg (fun _ => norm_nonneg _)), mul_comm]
        exact ENNReal.ofReal_eq_coe_nnreal _

lemma weakSchurKernel_bounds {𝕜 : Type} [RCLike 𝕜]
    {α T M : ℝ} (hα : 0 < α) (hT : 0 < T) (hM : 0 ≤ M)
    (k : C(Spec.triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M) :
    SchurLp.KernelBounds (intervalMeasure T) (intervalMeasure T) (weakSchurKernel hT.le α k)
      ⟨M * T ^ α / α, by positivity⟩ ⟨M * T ^ α / α, by positivity⟩ := by
  have hb := kernelBounds_of_lag_majorant T M hM (weakSchurKernel hT.le α k)
    (powerKernel α T) (measurable_powerKernel α T) (kernel_mass α T hα hT).1
    (weakSchurKernel_enorm_le hT.le α k hk)
  have hm := (kernel_mass α T hα hT).2.1
  have hA : (⟨M * ∫ r, ‖powerKernel α T r‖,
      mul_nonneg hM (integral_nonneg (fun _ => norm_nonneg _))⟩ : ℝ≥0) =
      ⟨M * T ^ α / α, by positivity⟩ := by
    apply Subtype.ext
    simp only
    rw [hm]
    ring
  simpa only [hA] using hb

lemma weakSchurKernel_bridge {𝕜 : Type} [RCLike 𝕜] {T t : ℝ}
    (hT : 0 ≤ T) (α : ℝ) (k : C(Spec.triangle T, 𝕜)) (f : ℝ → 𝕜)
    (ht : t ∈ Icc (0 : ℝ) T) :
    (Integrable (fun s => weakSchurKernel hT α k (t,s) * f s) (intervalMeasure T) ↔
      IntegrableOn (Spec.weakIntegrand α k f t) (Ioc 0 t)) ∧
    SchurLp.kernelValue (intervalMeasure T) (weakSchurKernel hT α k) f t =
      Spec.weakValue α k f t := by
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hμ : (intervalMeasure T).restrict (Ioc 0 t) = volume.restrict (Ioc 0 t) := by
    rw [intervalMeasure, Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub]
  have he : (fun s => weakSchurKernel hT α k (t,s) * f s) =ᵐ[intervalMeasure T]
      (Ioc 0 t).indicator (Spec.weakIntegrand α k f t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne t)] with s hsT hst
    by_cases hs : s ∈ Ioc (0 : ℝ) t
    · have hlag : t-s ∈ Ioc (0 : ℝ) T := by
        constructor
        · exact sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
        · linarith [hs.1, ht.2]
      simp only [weakSchurKernel, powerKernel, indicator_of_mem hlag,
        indicator_of_mem hs, Spec.weakIntegrand]
      rw [extendedAmplitude_eq hT k ⟨hs.1.le, hs.2, ht.2⟩, smul_mul_assoc]
    · have hlag : t-s ∉ Ioc (0 : ℝ) T := by
        intro h
        exact hs ⟨hsT.1, (sub_pos.mp h.1).le⟩
      simp [weakSchurKernel, powerKernel, hlag, hs]
  refine ⟨?_, ?_⟩
  · rw [integrable_congr he, integrable_indicator_iff measurableSet_Ioc]
    change Integrable _ ((intervalMeasure T).restrict (Ioc 0 t)) ↔ _
    rw [hμ]
    rfl
  · rw [SchurLp.kernelValue, integral_congr_ae he, integral_indicator measurableSet_Ioc]
    change (∫ s, Spec.weakIntegrand α k f t s ∂(intervalMeasure T).restrict (Ioc 0 t)) = _
    rw [hμ]
    rfl

lemma schurConstant_self (A : ℝ≥0) (p : ℝ≥0∞) : SchurLp.schurConstant A A p = A := by
  unfold SchurLp.schurConstant
  have he := Real.rpow_add' (x := (A : ℝ)) (y := 1 - (p⁻¹).toReal) (z := (p⁻¹).toReal) A.property (by ring_nf; norm_num)
  calc
    _ = (A : ℝ) ^ (1 - (p⁻¹).toReal + (p⁻¹).toReal) := he.symm
    _ = _ := by ring_nf; simp

/-- Lp bounded realization of the original weak kernel for positive length. -/
lemma weak_lp_construction_pos {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (hα : 0 < α) (hT : 0 < T)
    (k : C(Spec.triangle T, 𝕜)) (M : ℝ) (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
      (∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
        (∀ᵐ t ∂intervalMeasure T, IntegrableOn (Spec.weakIntegrand α k f t) (Ioc 0 t)) ∧
        (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f) ∧
      ‖V‖ ≤ M * T ^ α / α := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : BorelSpace 𝕜 := ⟨rfl⟩
  letI : IsFiniteMeasure (intervalMeasure T) := by unfold intervalMeasure; infer_instance
  let A : ℝ≥0 := ⟨M * T ^ α / α, by positivity⟩
  obtain ⟨F⟩ := SchurLp.schur_boundedness (intervalMeasure T) (intervalMeasure T)
    (weakSchurKernel hT.le α k) (measurable_weakSchurKernel hT.le α k) A A
    (weakSchurKernel_bounds hα hT hM k hk)
  refine ⟨F.op p, ?_, ?_⟩
  · intro f hf
    have hi := F.integral_exists p (hf.toLp f)
    have hr := F.represents p (hf.toLp f)
    have he := hf.coeFn_toLp
    constructor
    · filter_upwards [hi, ae_restrict_mem measurableSet_Ioc] with t hit ht
      apply (weakSchurKernel_bridge hT.le α k f ⟨ht.1.le, ht.2⟩).1.mp
      exact (SchurLp.kernel_integrable_congr _ _ he t).mp hit
    · filter_upwards [hr, ae_restrict_mem measurableSet_Ioc] with t hrt ht
      rw [hrt]
      rw [SchurLp.kernelValue_congr _ _ he]
      exact (weakSchurKernel_bridge hT.le α k f ⟨ht.1.le, ht.2⟩).2
  · exact (F.norm_le p).trans_eq (schurConstant_self A p)

/-- Bounded construction on every interval, retaining the zero-length case. -/
lemma weak_lp_construction {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (hα : 0 < α) (hT : 0 ≤ T)
    (k : C(Spec.triangle T, 𝕜)) (M : ℝ) (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
      (∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
        (∀ᵐ t ∂intervalMeasure T, IntegrableOn (Spec.weakIntegrand α k f t) (Ioc 0 t)) ∧
        (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f) ∧
      ‖V‖ ≤ M * T ^ α / α := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    refine ⟨0, ?_, ?_⟩
    · intro f hf
      constructor
      · simp [intervalMeasure]
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact (not_lt_of_ge ht.2 ht.1).elim
    · simp [Real.zero_rpow hα.ne']
  · exact weak_lp_construction_pos α T hα hT k M hM hk p


lemma lp_domination {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 < T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp 𝕜 p (intervalMeasure T))
    (g : ℝ → ℝ) (hg : MemLp g p (intervalMeasure T)) (C : ℝ)
    (hfg : ∀ᵐ s ∂intervalMeasure T, ‖f s‖ ≤ C * g s) :
    ∀ᵐ t ∂intervalMeasure T, ‖Spec.weakValue α k f t‖ ≤ (M*C) * powerValue α g t := by
  filter_upwards [(ExpandedFA.PartV.FractionalIntegrals.fractional_memLp hα hT p Fact.out g hg).1,
    ae_restrict_mem measurableSet_Ioc] with t hit ht
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hfg' := ae_restrict_of_ae_restrict_of_subset hsub hfg
  have hi : IntegrableOn (fun s => (t-s) ^ (α-1) * (M*C*g s)) (Ioc 0 t) := by
    simpa only [IntegrableOn, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hit.const_mul (M*C)
  calc
    ‖Spec.weakValue α k f t‖ ≤ ∫ s in Ioc 0 t, (t-s) ^ (α-1) * (M*C*g s) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [hfg', ae_restrict_mem measurableSet_Ioc] with s hs hsint
      rw [Spec.weakIntegrand, norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hsint.2) _)]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (sub_nonneg.mpr hsint.2) _)
      calc
        ‖Spec.amplitudeValue k t s * f s‖ ≤ M * ‖f s‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (amplitude_norm_le k hM hk _ _) (norm_nonneg _))
        _ ≤ M * (C*g s) := mul_le_mul_of_nonneg_left hs hM
        _ = _ := by ring
    _ = (M*C) * powerValue α g t := by
      simp only [powerValue, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      ext s
      ring

lemma lp_iterate_ae {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 < T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : ∀ f : Lp 𝕜 p (intervalMeasure T),
      (V f : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f) :
    ∀ (n : ℕ) (f : Lp 𝕜 p (intervalMeasure T)),
      ∀ᵐ t ∂intervalMeasure T,
        ‖((V ^ (n+1)) f : ℝ → 𝕜) t‖ ≤
          (M * Real.Gamma α) ^ (n+1) *
            fractionalValue (((n+1 : ℕ) : ℝ)*α) (fun s => ‖f s‖) t := by
  intro n
  induction n with
  | zero =>
    intro f
    have hh := lp_domination hα hT k hM hk p f (fun s => ‖f s‖) (Lp.memLp f).norm 1
      (Filter.Eventually.of_forall (fun s => by simp))
    filter_upwards [hh, hV f] with t ht hv
    simp only [zero_add, pow_one, Nat.cast_one, one_mul]
    rw [hv]
    convert ht using 1
    simp only [fractionalValue, smul_eq_mul]
    field_simp
  | succ n ih =>
    intro f
    let β : ℝ := ((n+1 : ℕ) : ℝ)*α
    have hβ : 0 < β := by dsimp [β]; positivity
    have hf : MemLp (fun s => ‖f s‖) p (intervalMeasure T) := (Lp.memLp f).norm
    have hg := (ExpandedFA.PartV.FractionalIntegrals.fractional_memLp hβ hT p Fact.out _ hf).2.1
    have hh := lp_domination hα hT k hM hk p ((V^(n+1)) f)
      (fractionalValue β (fun s => ‖f s‖)) hg ((M*Real.Gamma α)^(n+1)) (ih f)
    have hsem := ExpandedFA.PartV.BetaSemigroup.representative_semigroup
      α β T hα hβ hT.le p Fact.out (fun s => ‖f s‖) hf
    filter_upwards [hh, hV ((V^(n+1)) f), hsem] with t ht hv hs
    rw [pow_succ', mul_apply_eq_comp, hv]
    have hnorm : powerValue α (fractionalValue β (fun s => ‖f s‖)) t =
      Real.Gamma α * fractionalValue (α+β) (fun s => ‖f s‖) t := by
      rw [← hs]
      simp [fractionalValue, smul_eq_mul, (Real.Gamma_pos_of_pos hα).ne']
    rw [hnorm] at ht
    convert ht using 1
    have he : (((n+1+1 : ℕ) : ℝ)*α) = α+β := by dsimp [β]; push_cast; ring
    rw [he, pow_succ]
    ring

lemma lp_iterate_bound_pos {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 < T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : ∀ f : Lp 𝕜 p (intervalMeasure T),
      (V f : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f) :
    ∀ n : ℕ, ‖V ^ n‖ ≤ Spec.iterateBound α T M n := by
  intro n
  have hB : 0 ≤ Spec.iterateBound α T M n := by dsimp [Spec.iterateBound]; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  cases n with
  | zero => simp [Spec.iterateBound]
  | succ n =>
    let β : ℝ := ((n+1 : ℕ) : ℝ)*α
    let C : ℝ := (M*Real.Gamma α)^(n+1)
    have hβ : 0 < β := by dsimp [β]; positivity
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hJ : 0 ≤ operatorBound β T := by dsimp [operatorBound]; positivity
    have hh : eLpNorm ((V^(n+1)) f) p (intervalMeasure T) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (operatorBound β T) *
          eLpNorm f p (intervalMeasure T)) := by
      calc
        _ ≤ eLpNorm (fun t => C * fractionalValue β (fun s => ‖f s‖) t)
            p (intervalMeasure T) :=
          eLpNorm_mono_ae_real (Lp.aestronglyMeasurable _)
            (lp_iterate_ae hα hT k hM hk p V hV n f)
        _ = ENNReal.ofReal C * eLpNorm (fractionalValue β (fun s => ‖f s‖))
            p (intervalMeasure T) := by
          change eLpNorm (C • fractionalValue β (fun s => ‖f s‖)) p (intervalMeasure T) = _
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC]
        _ ≤ _ := by
          apply mul_le_mul' le_rfl
          simpa only [eLpNorm_norm _ (Lp.aestronglyMeasurable f)] using
            (ExpandedFA.PartV.FractionalIntegrals.fractional_memLp hβ hT p Fact.out (fun s => ‖f s‖) (Lp.memLp f).norm).2.2
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp f).ne)) hh
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hJ, ← Lp.norm_def, ← Lp.norm_def] at hreal
    convert hreal using 1
    dsimp [C, β, operatorBound, Spec.iterateBound]
    rw [mul_pow]
    ring

lemma lp_iterate_bound {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : ∀ f : Lp 𝕜 p (intervalMeasure T),
      (V f : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f) :
    ∀ n : ℕ, ‖V ^ n‖ ≤ Spec.iterateBound α T M n := by
  by_cases hp : 0 < T
  · exact lp_iterate_bound_pos hα hp k hM hk p V hV
  · have hz : intervalMeasure T = 0 := by
      simp [intervalMeasure, Ioc_eq_empty hp]
    intro n
    have hB : 0 ≤ Spec.iterateBound α T M n := by dsimp [Spec.iterateBound]; positivity
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro f
    simp only [Lp.norm_def, hz, eLpNorm_measure_zero, ENNReal.toReal_zero,
      mul_zero, le_refl]


open scoped BoundedContinuousFunction

section Inclusions
variable {𝕜 : Type} [RCLike 𝕜] {μ : Measure ℝ} [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]

def lpToL1Linear : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 1 μ where
  toFun f := ((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p)).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f+g)).mono_exponent (Fact.out : 1 ≤ p)),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p)),
      MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent (Fact.out : 1 ≤ p)),
      Lp.coeFn_add f g,
      Lp.coeFn_add (((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p)).toLp f)
        (((Lp.memLp g).mono_exponent (Fact.out : 1 ≤ p)).toLp g)] with x h1 h2 h3 h4 h5
    simpa only [h1,h4,h5, Pi.add_apply] using congrArg₂ (· + ·) h2.symm h3.symm
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_exponent (Fact.out : 1 ≤ p)),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p)),
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c (((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p)).toLp f)] with x h1 h2 h3 h4
    simpa only [h1,h3,h4, Pi.smul_apply, RingHom.id_apply] using congrArg (c • ·) h2.symm

lemma lpToL1Linear_bound (f : Lp 𝕜 p μ) :
    ‖lpToL1Linear p f‖ ≤ (μ Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := by
  change ‖((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p)).toLp f‖ ≤ _
  rw [Lp.norm_toLp]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : 1 ≤ p)
    (Lp.aestronglyMeasurable f)
  simp only [ENNReal.toReal_one, div_one] at h
  have hfin : μ univ ^ (1 - 1 / p.toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · have hp : (1 / p.toReal) ≤ 1 := by
        by_cases ht : p = ∞
        · simp [ht]
        · have hpr : 1 ≤ p.toReal := by exact_mod_cast (ENNReal.toReal_mono ht (Fact.out : 1 ≤ p))
          exact (div_le_one (by positivity)).mpr hpr
      linarith
    · exact measure_ne_top _ _
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top hfin) h
  rw [ENNReal.toReal_mul, mul_comm] at h'
  exact h'

def lpToL1 : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 1 μ :=
  (lpToL1Linear p).mkContinuous _ (lpToL1Linear_bound p)

lemma lpToL1_coe (f : Lp 𝕜 p μ) : (lpToL1 p f : ℝ → 𝕜) =ᵐ[μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p))

end Inclusions

instance intervalMeasureFinite (T : ℝ) : IsFiniteMeasure (intervalMeasure T) :=
  ⟨by simp [intervalMeasure]⟩

/-- Clamp extension into the bounded continuous functions on the line. -/
def intervalExtensionBounded {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] (ℝ →ᵇ 𝕜) :=
  (BoundedContinuousFunction.compContinuousCLM 𝕜 𝕜
    ⟨projIcc 0 T hT, continuous_projIcc⟩).comp
    (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) T) 𝕜 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

def intervalExtensionLp {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] Lp 𝕜 p (intervalMeasure T) := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : BorelSpace 𝕜 := ⟨rfl⟩
  exact (BoundedContinuousFunction.toLp p (intervalMeasure T) 𝕜).comp
    (intervalExtensionBounded hT)

lemma intervalExtensionLp_coe {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : C(Icc (0 : ℝ) T, 𝕜)) :
    (intervalExtensionLp hT p f : ℝ → 𝕜) =ᵐ[intervalMeasure T] continuousExtension hT f := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : BorelSpace 𝕜 := ⟨rfl⟩
  exact BoundedContinuousFunction.coeFn_toLp p (intervalMeasure T) 𝕜
    (intervalExtensionBounded hT f)

section L1Kernel
variable {𝕜 X Y : Type*} [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  (μ : Measure ℝ) (k : C(X × Y, 𝕜)) (q : C(ℝ, Y))

private def l1KernelSection : ℝ → C(X, 𝕜) := fun s =>
  ExpandedFA.PartV.ContinuousKernel.Spec.kernelSection k (q s)

private lemma l1KernelSection_continuous : Continuous (l1KernelSection k q) :=
  (ExpandedFA.PartV.ContinuousKernel.Spec.kernelSection k).continuous.comp q.continuous

private lemma l1KernelSection_bound (s : ℝ) : ‖l1KernelSection k q s‖ ≤ ‖k‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg k)).mpr
  intro x
  exact k.norm_coe_le_norm (x, q s)

private lemma l1KernelSection_integrable (f : Lp 𝕜 1 μ) :
    Integrable (fun s => f s • l1KernelSection k q s) μ := by
  exact (L1.integrable_coeFn f).smul_bdd ‖k‖
    (l1KernelSection_continuous k q).aestronglyMeasurable
    (Eventually.of_forall (l1KernelSection_bound k q))

private def l1KernelImage (f : Lp 𝕜 1 μ) : C(X, 𝕜) :=
  ∫ s, f s • l1KernelSection k q s ∂μ

private lemma l1KernelImage_bound (f : Lp 𝕜 1 μ) :
    ‖l1KernelImage μ k q f‖ ≤ ‖k‖ * ‖f‖ := by
  calc
    _ ≤ ∫ s, ‖f s‖ * ‖k‖ ∂μ := by
      apply norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const ‖k‖)
      apply Eventually.of_forall
      intro s
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (l1KernelSection_bound k q s) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, ← L1.norm_eq_integral_norm]; ring

private def l1KernelLinearMap : Lp 𝕜 1 μ →ₗ[𝕜] C(X, 𝕜) where
  toFun := l1KernelImage μ k q
  map_add' f g := by
    change (∫ s, (f+g) s • l1KernelSection k q s ∂μ) = _
    calc
      _ = ∫ s, (f s + g s) • l1KernelSection k q s ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with s hs
        rw [hs]
        rfl
      _ = _ := by
        simp_rw [add_smul]
        exact integral_add (l1KernelSection_integrable μ k q f)
          (l1KernelSection_integrable μ k q g)
  map_smul' c f := by
    change (∫ s, (c • f) s • l1KernelSection k q s ∂μ) = _
    calc
      _ = ∫ s, (c • f s) • l1KernelSection k q s ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with s hs
        rw [hs]
        rfl
      _ = _ := by
        change (∫ s, (c * f s) • l1KernelSection k q s ∂μ) =
          c • (∫ s, f s • l1KernelSection k q s ∂μ)
        simp_rw [mul_smul]
        exact integral_smul c (fun s => f s • l1KernelSection k q s)


/-- Continuous-kernel operator from L1 into continuous functions, allowing a
continuous ambient parametrization of the compact integration domain. -/
def continuousKernelL1 : Lp 𝕜 1 μ →L[𝕜] C(X, 𝕜) :=
  (l1KernelLinearMap μ k q).mkContinuous ‖k‖ (l1KernelImage_bound μ k q)

lemma continuousKernelL1_integrable (f : Lp 𝕜 1 μ) (x : X) :
    Integrable (fun s => k (x,q s) * f s) μ := by
  exact (L1.integrable_coeFn f).bdd_mul
    ((k.continuous.comp (continuous_const.prodMk q.continuous)).aestronglyMeasurable)
    (Eventually.of_forall fun s => k.norm_coe_le_norm (x, q s))

lemma continuousKernelL1_apply (f : Lp 𝕜 1 μ) (x : X) :
    continuousKernelL1 μ k q f x = ∫ s, k (x,q s) * f s ∂μ := by
  change l1KernelImage μ k q f x = _
  rw [l1KernelImage, ContinuousMap.integral_apply (l1KernelSection_integrable μ k q f)]
  simp [l1KernelSection, ExpandedFA.PartV.ContinuousKernel.Spec.kernelSection, mul_comm]

lemma continuousKernelL1_norm_le : ‖continuousKernelL1 μ k q‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg k) _

lemma continuousKernelL1_dist_le (f : Lp 𝕜 1 μ) (x x' : X) :
    dist (continuousKernelL1 μ k q f x) (continuousKernelL1 μ k q f x') ≤
      dist (k.curry x) (k.curry x') * ‖f‖ := by
  rw [dist_eq_norm, continuousKernelL1_apply, continuousKernelL1_apply,
    ← integral_sub (continuousKernelL1_integrable μ k q f x)
      (continuousKernelL1_integrable μ k q f x')]
  calc
    _ ≤ ∫ s, ‖f s‖ * ‖k.curry x - k.curry x'‖ ∂μ := by
      apply norm_integral_le_of_norm_le
        ((L1.integrable_coeFn f).norm.mul_const ‖k.curry x - k.curry x'‖)
      apply Eventually.of_forall
      intro s
      rw [← sub_mul, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left
        ((k.curry x - k.curry x').norm_coe_le_norm (q s)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, ← L1.norm_eq_integral_norm, dist_eq_norm]; ring

lemma continuousKernelL1_isCompact : IsCompactOperator (continuousKernelL1 μ k q) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall _ zero_lt_one).mpr
  apply (ExpandedFA.PartV.Ascoli.arzela_ascoli 𝕜 X
    (continuousKernelL1 μ k q '' Metric.closedBall 0 1)).mpr
  constructor
  · refine ⟨‖continuousKernelL1 μ k q‖, norm_nonneg _, ?_⟩
    rintro g ⟨f, hf, rfl⟩ x
    have hf' : ‖f‖ ≤ 1 := by simpa using hf
    exact ((continuousKernelL1 μ k q f).norm_coe_le_norm x).trans
      (((continuousKernelL1 μ k q).le_opNorm f).trans (by
        simpa using mul_le_mul_of_nonneg_left hf' (norm_nonneg _)))
  · intro x₀
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun x => dist (k.curry x₀) (k.curry x))
    · have h : Continuous (fun x => dist (k.curry x₀) (k.curry x)) :=
        continuous_const.dist k.curry.continuous
      simpa using (h.continuousAt (x := x₀)).tendsto
    · filter_upwards with x g
      obtain ⟨f, hf, hfg⟩ := g.property
      have hf' : ‖f‖ ≤ 1 := by simpa using hf
      change dist ((g : C(X, 𝕜)) x₀) ((g : C(X, 𝕜)) x) ≤ _
      rw [← hfg]
      exact (continuousKernelL1_dist_le μ k q f x₀ x).trans (by
        simpa using mul_le_mul_of_nonneg_left hf' dist_nonneg)
end L1Kernel

/-- Compact cutoff realization on the original ambient Lp quotient. -/
def cutoffLpOperator {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T) :=
  (intervalExtensionLp hT p).comp
    ((continuousKernelL1 (intervalMeasure T) (cutoffKernel hα hT hδ k)
      ⟨projIcc 0 T hT, continuous_projIcc⟩).comp (lpToL1 p))

lemma cutoffLpOperator_isCompact {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : IsCompactOperator (cutoffLpOperator hα hT hδ k p) := by
  exact ((continuousKernelL1_isCompact (intervalMeasure T) (cutoffKernel hα hT hδ k)
    ⟨projIcc 0 T hT, continuous_projIcc⟩).comp_clm (lpToL1 p)).clm_comp
      (intervalExtensionLp hT p)

lemma cutoffLpOperator_represents {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp 𝕜 p (intervalMeasure T)) :
    (cutoffLpOperator hα hT hδ k p f : ℝ → 𝕜) =ᵐ[intervalMeasure T]
      (fun t => ∫ s, (cutoffPower α δ (t-s) • extendedAmplitude hT k (t,s)) * f s
        ∂intervalMeasure T) := by
  have he := intervalExtensionLp_coe hT p
    (continuousKernelL1 (intervalMeasure T) (cutoffKernel hα hT hδ k)
      ⟨projIcc 0 T hT, continuous_projIcc⟩ (lpToL1 p f))
  filter_upwards [he, ae_restrict_mem measurableSet_Ioc] with t het ht
  simp only [cutoffLpOperator, ContinuousLinearMap.comp_apply]
  rw [het]
  change continuousKernelL1 _ _ _ _ (projIcc 0 T hT t) = _
  rw [continuousKernelL1_apply]
  apply integral_congr_ae
  filter_upwards [lpToL1_coe p f, ae_restrict_mem measurableSet_Ioc] with s hes hs
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le,ht.2⟩
  have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le,hs.2⟩
  simp only [cutoffKernel, ContinuousMap.coe_mk, projIcc_of_mem hT ht',
    projIcc_of_mem hT hs', Subtype.coe_mk, hes]

lemma cutoffLpOperator_integrable {𝕜 : Type} [RCLike 𝕜] {α T δ : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp 𝕜 p (intervalMeasure T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Integrable (fun s => (cutoffPower α δ (t-s) • extendedAmplitude hT k (t,s)) * f s)
      (intervalMeasure T) := by
  have hi := continuousKernelL1_integrable (intervalMeasure T) (cutoffKernel hα hT hδ k)
    ⟨projIcc 0 T hT, continuous_projIcc⟩ (lpToL1 p f) ⟨t,ht⟩
  apply hi.congr
  filter_upwards [lpToL1_coe p f, ae_restrict_mem measurableSet_Ioc] with s hes hs
  have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le,hs.2⟩
  simp only [cutoffKernel, ContinuousMap.coe_mk, projIcc_of_mem hT hs',
    Subtype.coe_mk, hes]


open ExpandedFA.PartV.FractionalIntegrals.Spec

/-- The formula alone identifies a bounded realization with the Schur operator,
so a lag majorant controls its operator norm. -/
lemma lp_operator_norm_le_of_lag_majorant {𝕜 : Type} [RCLike 𝕜]
    (T M : ℝ) (hM : 0 ≤ M) (q : ℝ × ℝ → 𝕜)
    (hqm : Measurable q) (w : ℝ → ℝ) (hwm : Measurable w) (hwi : Integrable w volume)
    (hq : ∀ z, ‖q z‖ₑ ≤ ‖w (z.1-z.2)‖ₑ * ENNReal.ofReal M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hF : ∀ f, (F f : ℝ → 𝕜) =ᵐ[intervalMeasure T]
      SchurLp.kernelValue (intervalMeasure T) q f) :
    ‖F‖ ≤ M * ∫ r, ‖w r‖ := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : BorelSpace 𝕜 := ⟨rfl⟩
  letI : IsFiniteMeasure (intervalMeasure T) := by unfold intervalMeasure; infer_instance
  let A : ℝ≥0 := ⟨M * ∫ r, ‖w r‖, mul_nonneg hM (integral_nonneg (fun _ => norm_nonneg _))⟩
  obtain ⟨H⟩ := SchurLp.schur_boundedness (intervalMeasure T) (intervalMeasure T) q hqm A A
    (kernelBounds_of_lag_majorant T M hM q w hwm hwi hq)
  have heq : F = H.op p := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hF f).trans (H.represents p f).symm
  rw [heq]
  exact (H.norm_le p).trans_eq (schurConstant_self A p)

/-- A quantitative norm estimate for the difference of two realizations. -/
lemma lp_operator_sub_norm_le_of_lag_majorant {𝕜 : Type} [RCLike 𝕜]
    (T M : ℝ) (hM : 0 ≤ M) (q₁ q₂ : ℝ × ℝ → 𝕜)
    (hqm : Measurable (q₁-q₂)) (w : ℝ → ℝ)
    (hwm : Measurable w) (hwi : Integrable w volume)
    (hq : ∀ z, ‖q₁ z-q₂ z‖ₑ ≤ ‖w (z.1-z.2)‖ₑ * ENNReal.ofReal M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F G : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hFi : ∀ f : Lp 𝕜 p (intervalMeasure T), ∀ᵐ t ∂intervalMeasure T,
      Integrable (fun s => q₁ (t,s) * f s) (intervalMeasure T))
    (hGi : ∀ f : Lp 𝕜 p (intervalMeasure T), ∀ᵐ t ∂intervalMeasure T,
      Integrable (fun s => q₂ (t,s) * f s) (intervalMeasure T))
    (hF : ∀ f, (F f : ℝ → 𝕜) =ᵐ[intervalMeasure T]
      SchurLp.kernelValue (intervalMeasure T) q₁ f)
    (hG : ∀ f, (G f : ℝ → 𝕜) =ᵐ[intervalMeasure T]
      SchurLp.kernelValue (intervalMeasure T) q₂ f) :
    ‖F-G‖ ≤ M * ∫ r, ‖w r‖ := by
  apply lp_operator_norm_le_of_lag_majorant T M hM (q₁-q₂) hqm w hwm hwi hq p (F-G)
  intro f
  filter_upwards [Lp.coeFn_sub (F f) (G f), hF f, hG f, hFi f, hGi f] with t ht hft hgt hit hjt
  change (F f - G f : Lp 𝕜 p (intervalMeasure T)) t = _
  rw [ht]
  simp only [Pi.sub_apply, hft, hgt, SchurLp.kernelValue]
  rw [← integral_sub hit hjt]
  congr 1
  funext s
  simp only [Pi.sub_apply, sub_mul]



/-- The cutoff kernel with a lag restriction for global Schur estimates. -/
def weakCutoffSchurKernel {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (α δ : ℝ) (k : C(Spec.triangle T, 𝕜)) (z : ℝ × ℝ) : 𝕜 :=
  ((Ioc (0 : ℝ) T).indicator (cutoffPower α δ)) (z.1-z.2) • extendedAmplitude hT k z

/-- Signed radial difference; its norm is the discarded-strip majorant. -/
def cutoffLagError (α T δ : ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) T).indicator (fun r => r ^ (α-1) - cutoffPower α δ r)

lemma measurable_weakCutoffSchurKernel {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] {α T δ : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ)
    (k : C(Spec.triangle T, 𝕜)) : Measurable (weakCutoffSchurKernel hT α δ k) :=
  ((((continuous_cutoffPower hα hδ).measurable).indicator measurableSet_Ioc).comp
    (measurable_fst.sub measurable_snd)).smul (continuous_extendedAmplitude hT k).measurable

lemma cutoffLagError_measurable {α T δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    Measurable (cutoffLagError α T δ) :=
  ((measurable_id.pow_const _).sub (continuous_cutoffPower hα hδ).measurable).indicator
    measurableSet_Ioc

lemma cutoffLagError_integrable {α T δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    Integrable (cutoffLagError α T δ) volume := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact (power_integrable hα).sub (continuous_cutoffPower hα hδ).integrableOn_Ioc

lemma cutoffLagError_mass (α T δ : ℝ) :
    (∫ r, ‖cutoffLagError α T δ r‖) =
      ∫ r in Ioc 0 T, |r ^ (α-1) - cutoffPower α δ r| := by
  simp only [cutoffLagError, norm_indicator_eq_indicator_norm]
  rw [integral_indicator measurableSet_Ioc]
  rfl

lemma weakSchurKernel_sub_cutoff_enorm_le {𝕜 : Type} [RCLike 𝕜]
    {α T δ M : ℝ} (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (hk : ∀ z, ‖k z‖ ≤ M) (z : ℝ × ℝ) :
    ‖weakSchurKernel hT α k z - weakCutoffSchurKernel hT α δ k z‖ₑ ≤
      ‖cutoffLagError α T δ (z.1-z.2)‖ₑ * ENNReal.ofReal M := by
  have he : weakSchurKernel hT α k z - weakCutoffSchurKernel hT α δ k z =
      cutoffLagError α T δ (z.1-z.2) • extendedAmplitude hT k z := by
    by_cases hz : z.1-z.2 ∈ Ioc (0 : ℝ) T
    · simp [weakSchurKernel, weakCutoffSchurKernel, cutoffLagError, powerKernel, hz, sub_smul]
    · simp [weakSchurKernel, weakCutoffSchurKernel, cutoffLagError, powerKernel, hz]
  rw [he, enorm_smul]
  apply mul_le_mul_right
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hk _)

lemma weakCutoffSchurKernel_eq {𝕜 : Type} [RCLike 𝕜] {α T δ t s : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (_hδ : 0 < δ) (k : C(Spec.triangle T, 𝕜))
    (ht : t ∈ Icc (0 : ℝ) T) (hs : s ∈ Icc (0 : ℝ) T) :
    weakCutoffSchurKernel hT α δ k (t,s) =
      cutoffPower α δ (t-s) • extendedAmplitude hT k (t,s) := by
  by_cases hlag : 0 < t-s
  · have hm : t-s ∈ Ioc (0 : ℝ) T := ⟨hlag, by linarith [ht.2, hs.1]⟩
    simp [weakCutoffSchurKernel, hm]
  · have hz := cutoffPower_zero (δ := δ) hα (le_of_not_gt hlag)
    simp [weakCutoffSchurKernel, hz]



lemma cutoffLpOperator_error_of_majorant {𝕜 : Type} [RCLike 𝕜] {α T δ M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ)
    (k : C(Spec.triangle T, 𝕜)) (hM : 0 ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : ∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
      (∀ᵐ t ∂intervalMeasure T, IntegrableOn (Spec.weakIntegrand α k f t) (Ioc 0 t)) ∧
      (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f)
    (q : ℝ × ℝ → 𝕜)
    (hq : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T,
      q (t,s) = cutoffPower α δ (t-s) • extendedAmplitude hT k (t,s))
    (hqm : Measurable (weakSchurKernel hT α k - q))
    (w : ℝ → ℝ) (hwm : Measurable w) (hwi : Integrable w volume)
    (hbound : ∀ z, ‖weakSchurKernel hT α k z - q z‖ₑ ≤
      ‖w (z.1-z.2)‖ₑ * ENNReal.ofReal M) :
    ‖V-cutoffLpOperator hα hT hδ k p‖ ≤ M * ∫ r, ‖w r‖ := by
  have hv (f : Lp 𝕜 p (intervalMeasure T)) := hV f (Lp.memLp f)
  simp only [Lp.toLp_coeFn] at hv
  apply lp_operator_sub_norm_le_of_lag_majorant T M hM (weakSchurKernel hT α k)
    q hqm w hwm hwi hbound p V (cutoffLpOperator hα hT hδ k p)
  · intro f
    filter_upwards [(hv f).1, ae_restrict_mem measurableSet_Ioc] with t hit ht
    exact (weakSchurKernel_bridge hT α k f ⟨ht.1.le,ht.2⟩).1.mpr hit
  · intro f
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply (cutoffLpOperator_integrable hα hT hδ k p f ⟨ht.1.le,ht.2⟩).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [hq t ⟨ht.1.le,ht.2⟩ s ⟨hs.1.le,hs.2⟩]
  · intro f
    filter_upwards [(hv f).2, ae_restrict_mem measurableSet_Ioc] with t ht htI
    rw [ht]
    exact (weakSchurKernel_bridge hT α k f ⟨htI.1.le,htI.2⟩).2.symm
  · intro f
    filter_upwards [cutoffLpOperator_represents hα hT hδ k p f,
      ae_restrict_mem measurableSet_Ioc] with t ht htI
    rw [ht]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [hq t ⟨htI.1.le,htI.2⟩ s ⟨hs.1.le,hs.2⟩]

lemma cutoffLpOperator_error_bound {𝕜 : Type} [RCLike 𝕜] {α T δ M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hδ : 0 < δ)
    (k : C(Spec.triangle T, 𝕜)) (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : ∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
      (∀ᵐ t ∂intervalMeasure T, IntegrableOn (Spec.weakIntegrand α k f t) (Ioc 0 t)) ∧
      (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f) :
    ‖V-cutoffLpOperator hα hT hδ k p‖ ≤
      M * ∫ r in Ioc 0 T, |r ^ (α-1)-cutoffPower α δ r| := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : BorelSpace 𝕜 := ⟨rfl⟩
  have h := cutoffLpOperator_error_of_majorant hα hT hδ k hM p V hV
    (weakCutoffSchurKernel hT α δ k)
    (fun t ht s hs => weakCutoffSchurKernel_eq hα hT hδ k ht hs)
    ((measurable_weakSchurKernel hT α k).sub
      (measurable_weakCutoffSchurKernel hα hT hδ k))
    (cutoffLagError α T δ) (cutoffLagError_measurable hα hδ)
    (cutoffLagError_integrable hα hδ)
    (weakSchurKernel_sub_cutoff_enorm_le hT k hk)
  rw [cutoffLagError_mass α T δ] at h
  exact h

/-- Compactness follows from compact continuous cutoffs in operator norm,
with the same estimate at both Lp endpoints. -/
lemma lp_isCompact {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(Spec.triangle T, 𝕜))
    (hM : 0 ≤ M) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : ∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
      (∀ᵐ t ∂intervalMeasure T, IntegrableOn (Spec.weakIntegrand α k f t) (Ioc 0 t)) ∧
      (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f) :
    IsCompactOperator V := by
  have hd (n : ℕ) : 0 < (n+1 : ℝ)⁻¹ := by positivity
  let A (n : ℕ) := cutoffLpOperator hα hT (hd n) k p
  have hAc (n : ℕ) : IsCompactOperator (A n) :=
    cutoffLpOperator_isCompact hα hT (hd n) k p
  have he : Tendsto (fun n : ℕ => ‖V-A n‖) atTop (𝓝 0) := by
    apply squeeze_zero (f := fun n : ℕ => ‖V-A n‖)
      (g := fun n => M * ∫ r in Ioc 0 T,
        |r ^ (α-1)-cutoffPower α ((n+1 : ℝ)⁻¹) r|)
      (fun n => norm_nonneg (V-A n))
      (fun n => cutoffLpOperator_error_bound hα hT (hd n) k hM hk p V hV)
    simpa using (cutoffPower_error_tendsto (T := T) hα).const_mul M
  apply isCompactOperator_of_tendsto (l := atTop) (F := A) ?_
    (Eventually.of_forall hAc)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using he

/-- Full weakly singular Volterra theorem on every Lp quotient, including
p=1 and p=infinity, with the unnormalized kernel and exact Gamma bound. -/
theorem lp_theorem : Spec.LpTheorem := by
  intro 𝕜 _ α T hα hT k M hM hk p _
  obtain ⟨V, hf, _⟩ := weak_lp_construction α T hα hT k M hM hk p
  have hV : ∀ f : Lp 𝕜 p (intervalMeasure T),
      (V f : ℝ → 𝕜) =ᵐ[intervalMeasure T] Spec.weakValue α k f := by
    intro f
    simpa only [Lp.toLp_coeFn] using (hf f (Lp.memLp f)).2
  have hb := lp_iterate_bound hα hT k hM hk p V hV
  exact ⟨V, hf, lp_isCompact hα hT k hM hk p V hf, hb,
    resolvent_properties_of_iterate_bound hα hT hM V hb⟩

end ExpandedFA.PartV.WeakVolterraBounds
