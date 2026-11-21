import MathGenome.Internal.LinearPDE.P201Specs.Heat.OrderedTraceChain
import MathGenome.Internal.LinearPDE.P201.Elliptic.Truncation
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace P201.OrderedTraceChain

abbrev positiveL2 := @P201Specs.OrderedTraceChain.positiveL2
abbrev zeroPositive := @P201Specs.OrderedTraceChain.zeroPositive

/-- The L² truncation used here is the same quotient map as E04. -/
theorem positiveL2_eq {n : ℕ} (Ω : Domain n) (u : Lp ℝ Ω 2) :
    positiveL2 Ω u = Truncation.positiveLp u := by
  apply MeasureTheory.Lp.ext
  exact (MeasureTheory.Lp.coeFn_posPart u).trans (Truncation.positiveLp_ae u).symm

/-- Positive part is 1-Lipschitz on the spatial L² space. -/
theorem positiveL2_lipschitz {n : ℕ} (Ω : Domain n) :
    LipschitzWith 1 (positiveL2 Ω) :=
  (LipschitzWith.id.max_const (0 : ℝ)).lipschitzWith_compLp (max_eq_right le_rfl)

theorem positiveL2_norm_sub_le {n : ℕ} (Ω : Domain n) (u v : Lp ℝ Ω 2) :
    ‖positiveL2 Ω u - positiveL2 Ω v‖ ≤ ‖u - v‖ := by
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    (positiveL2_lipschitz Ω).dist_le_mul u v

/-- The continuous representative is truncated at every time, including the
endpoints, rather than selected from an arbitrary Bochner representative. -/
theorem positiveL2_continuousOn {n : ℕ} (Ω : Domain n) {U : ℝ → Lp ℝ Ω 2}
    {S : Set ℝ} (hU : ContinuousOn U S) :
    ContinuousOn (fun t => positiveL2 Ω (U t)) S :=
  (positiveL2_lipschitz Ω).continuous.comp_continuousOn hU

/-- On a signed-trace function the auxiliary projection does nothing. -/
theorem zeroPositive_val {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) (htr : P201Specs.Trace.AgreesWithSmooth tr)
    (u : H ℝ Ω 1)
    (hu : ∀ᵐ x ∂boundaryMeasure Ω, P201Specs.Trace.inclusion Ω hΩ (tr u) x ≤ 0) :
    (zeroPositive Ω u).val = Truncation.positivePart Ω u := by
  have hz : (P201Specs.Trace.inclusion Ω hΩ (tr (0 : H ℝ Ω 1)) : Space (m + 1) → ℝ)
      =ᵐ[boundaryMeasure Ω] 0 := by
    simpa only [map_zero] using MeasureTheory.Lp.coeFn_zero ℝ 2 (boundaryMeasure Ω)
  have hord : ∀ᵐ x ∂boundaryMeasure Ω,
      P201Specs.Trace.inclusion Ω hΩ (tr u) x ≤
        P201Specs.Trace.inclusion Ω hΩ (tr (0 : H ℝ Ω 1)) x := by
    filter_upwards [hu, hz] with x hx hz
    simpa only [hz, Pi.zero_apply] using hx
  have hp : Truncation.positivePart Ω u ∈ P201Specs.hZeroSubmodule ℝ Ω := by
    simpa only [sub_zero] using Truncation.ordered_trace Ω hΩ tr htr u 0 hord
  exact congrArg Subtype.val
    ((P201Specs.hZeroSubmodule ℝ Ω).orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨Truncation.positivePart Ω u, hp⟩)

/-- Full H¹ norm contraction toward the origin. This does not assert the
false claim that truncation is Lipschitz in the full H¹ difference norm. -/
theorem positivePart_norm_le {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    ‖Truncation.positivePart Ω u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [P201.fullHilbertNorm (𝕜 := ℝ) Ω 1, P201.fullHilbertNorm (𝕜 := ℝ) Ω 1]
  apply Finset.sum_le_sum
  intro α _
  apply pow_le_pow_left₀ (norm_nonneg _)
  by_cases hz : α.val = 0
  · have ha : α = P102.U4.zeroSobolevIndex n 1 := Subtype.ext hz
    subst α
    change ‖hUnderlying Ω 1 (Truncation.positivePart Ω u)‖ ≤ ‖hUnderlying Ω 1 u‖
    rw [Truncation.underlying_positiveLp]
    apply MeasureTheory.Lp.norm_le_norm_of_ae_le
    filter_upwards [Truncation.positiveLp_ae (hUnderlying Ω 1 u)] with x hx
    rw [hx]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  · have hc : α.val.card = 1 := by
      have := α.property
      have hn := Multiset.card_eq_zero.not.mpr hz
      omega
    obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hc
    have ha : α = ⟨{j}, by simp⟩ := Subtype.ext hj
    subst α
    change ‖hFirstDerivative (Truncation.positivePart Ω u) j‖ ≤ ‖hFirstDerivative u j‖
    apply MeasureTheory.Lp.norm_le_norm_of_ae_le
    filter_upwards [Truncation.positivePart_derivative Ω u j] with x hx
    rw [hx]
    split_ifs <;> simp

theorem zeroPositive_continuous {n : ℕ} (Ω : Domain n) :
    Continuous (zeroPositive Ω) :=
  (P201Specs.hZeroSubmodule ℝ Ω).orthogonalProjectionOnto.continuous.comp
    (Truncation.positivePart_continuous Ω)

theorem zeroPositive_norm_le {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    ‖zeroPositive Ω u‖ ≤ ‖u‖ :=
  ((P201Specs.hZeroSubmodule ℝ Ω).norm_orthogonalProjectionOnto_apply_le
    (Truncation.positivePart Ω u)).trans (positivePart_norm_le Ω u)

/-- Strong Bochner measurability and integrability follow from continuity
and the full H¹ norm bound, with no extra time regularity assumption. -/
theorem zeroPositive_memLp {n : ℕ} (Ω : Domain n) {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {w : X → H ℝ Ω 1} (hw : MemLp w 2 μ) :
    MemLp (fun t => zeroPositive Ω (w t)) 2 μ :=
  hw.of_le ((zeroPositive_continuous Ω).comp_aestronglyMeasurable hw.aestronglyMeasurable)
    (Eventually.of_forall fun t => zeroPositive_norm_le Ω (w t))

/-- Hölder's inequality for the actual continuous-dual evaluation. -/
theorem dual_pairing_integrable {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    {d : X → (E →L[ℝ] ℝ)} {v : X → E} (hd : MemLp d 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun t => d t (v t)) μ := by
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).memLp_of_bilin (p := 2) (q := 2) 1 hd hv)

/-- All membership conclusions of the ordered-trace chain rule, with
the exact continuous representative and genuine dual pairing. -/
theorem membership : P201Specs.OrderedTraceChain.MembershipStatement := by
  intro m Ω hΩ tr htr T w du U hw hdu hU hrep hsign
  have hv := zeroPositive_memLp Ω hw
  have hval : ∀ᵐ t ∂P201Specs.OrderedTraceChain.timeMeasure T,
      (zeroPositive Ω (w t)).val = Truncation.positivePart Ω (w t) := by
    filter_upwards [hsign] with t ht
    exact zeroPositive_val Ω hΩ tr htr (w t) ht
  refine ⟨hv, hval, positiveL2_continuousOn Ω hU, ?_, ?_⟩
  · filter_upwards [hval, hrep] with t ht hUt
    change hUnderlying Ω 1 (zeroPositive Ω (w t)).val = positiveL2 Ω (U t)
    rw [ht, hUt, positiveL2_eq, Truncation.underlying_positiveLp]
  · letI : NormedSpace ℝ (H10 ℝ Ω) := inferInstanceAs
      (NormedSpace ℝ ↥(P201Specs.hZeroSubmodule ℝ Ω))
    exact dual_pairing_integrable (E := H10 ℝ Ω) hdu hv

/-- Continuous norm-bounded nonlinear maps preserve strong L² convergence
on a finite measure space. Vitali handles varying, rather than fixed,
dominating functions. -/
theorem continuous_comp_tendsto_L2 {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure X} [IsFiniteMeasure μ] (g : E → F) (hg : Continuous g)
    (hb : ∀ x, ‖g x‖ ≤ ‖x‖) (f : ℕ → X → E) (a : X → E)
    (hf : ∀ k, MemLp (f k) 2 μ) (ha : MemLp a 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - a) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => g (f k x) - g (a x)) 2 μ) atTop (𝓝 0) := by
  have hgf (k) : MemLp (fun x => g (f k x)) 2 μ :=
    (hf k).of_le (hg.comp_aestronglyMeasurable (hf k).aestronglyMeasurable)
      (Eventually.of_forall fun x => hb (f k x))
  have hga : MemLp (fun x => g (a x)) 2 μ :=
    ha.of_le (hg.comp_aestronglyMeasurable ha.aestronglyMeasurable)
      (Eventually.of_forall fun x => hb (a x))
  have hui := unifIntegrable_of_tendsto_Lp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf ha hlim
  have hgui : UnifIntegrable (fun k x => g (f k x)) 2 μ := by
    apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := unifIntegrable_iff.mp hui ε hε
    refine ⟨δ, hδ, fun k s hs => ?_⟩
    exact (eLpNorm_mono ((hgf k).aestronglyMeasurable.restrict) (fun x => hb (f k x))).trans
      (hd k s hs)
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (hlim.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun k => (hgf (ns (ms k))).aestronglyMeasurable) hga (hgui.comp (fun k => ns (ms k)))
  filter_upwards [hae] with x hx
  exact (hg.tendsto (a x)).comp hx

/-- The full H¹ positive-part map is continuous also on L² in time,
including all weak derivative coordinates. -/
theorem positivePart_time_tendsto {n : ℕ} (Ω : Domain n) (T : ℝ)
    (w : ℕ → ℝ → H ℝ Ω 1) (v : ℝ → H ℝ Ω 1)
    (hw : ∀ k, MemLp (w k) 2 (P201Specs.OrderedTraceChain.timeMeasure T))
    (hv : MemLp v 2 (P201Specs.OrderedTraceChain.timeMeasure T))
    (hlim : Tendsto (fun k => eLpNorm (w k - v) 2
      (P201Specs.OrderedTraceChain.timeMeasure T)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      (fun t => Truncation.positivePart Ω (w k t) - Truncation.positivePart Ω (v t))
      2 (P201Specs.OrderedTraceChain.timeMeasure T)) atTop (𝓝 0) :=
  continuous_comp_tendsto_L2 (Truncation.positivePart Ω)
    (Truncation.positivePart_continuous Ω) (positivePart_norm_le Ω) w v hw hv hlim

/-- Strong convergence of both L² factors passes the actual integrated dual
pairing to the limit. No pointwise convergence of derivatives is needed. -/
theorem dual_pairing_integral_tendsto {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    (d : ℕ → MeasureTheory.Lp (E →L[ℝ] ℝ) 2 μ) (v : ℕ → MeasureTheory.Lp E 2 μ)
    (a : MeasureTheory.Lp (E →L[ℝ] ℝ) 2 μ) (b : MeasureTheory.Lp E 2 μ)
    (hd : Tendsto d atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun k => ∫ t, d k t (v k t) ∂μ) atTop (𝓝 (∫ t, a t (b t) ∂μ)) := by
  let B := ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)
  have h := ((B.lpPairing μ 2 2).continuous₂.tendsto (a, b)).comp (hd.prodMk_nhds hv)
  simpa only [Function.comp_apply, Function.comp_def, Function.uncurry_apply_pair,
    ContinuousLinearMap.lpPairing_eq_integral,
    B, ContinuousLinearMap.id_apply] using h

/-- Endpoint energy identities pass to strong dual/zero-trace limits. -/
theorem energy_identity_of_limits {X E Y : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] (μ : Measure X)
    (d : ℕ → MeasureTheory.Lp (E →L[ℝ] ℝ) 2 μ) (v : ℕ → MeasureTheory.Lp E 2 μ)
    (a : MeasureTheory.Lp (E →L[ℝ] ℝ) 2 μ) (b : MeasureTheory.Lp E 2 μ)
    (p q : ℕ → Y) (p₀ q₀ : Y)
    (hd : Tendsto d atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto q atTop (𝓝 q₀))
    (he : ∀ k, (1 / 2 : ℝ) * ‖p k‖ ^ 2 - (1 / 2 : ℝ) * ‖q k‖ ^ 2 =
      ∫ t, d k t (v k t) ∂μ) :
    (1 / 2 : ℝ) * ‖p₀‖ ^ 2 - (1 / 2 : ℝ) * ‖q₀‖ ^ 2 =
      ∫ t, a t (b t) ∂μ := by
  have hl := (hp.norm.pow 2).const_mul (1 / 2 : ℝ) |>.sub
    ((hq.norm.pow 2).const_mul (1 / 2 : ℝ))
  have hr := dual_pairing_integral_tendsto μ d v a b hd hv
  exact tendsto_nhds_unique hl (by simpa only [he] using hr)

/-- Raw-function version of the strong dual-pairing limit. Keeping quotient
representatives inside this general lemma avoids concrete-submodule choices
in the time-regularization assembly. -/
theorem dual_pairing_integral_tendsto_functions {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    (d : ℕ → X → (E →L[ℝ] ℝ)) (v : ℕ → X → E)
    (a : X → (E →L[ℝ] ℝ)) (b : X → E)
    (hd : ∀ k, MemLp (d k) 2 μ) (hv : ∀ k, MemLp (v k) 2 μ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hda : Tendsto (fun k => eLpNorm (d k - a) 2 μ) atTop (𝓝 0))
    (hvb : Tendsto (fun k => eLpNorm (v k - b) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t, d k t (v k t) ∂μ) atTop (𝓝 (∫ t, a t (b t) ∂μ)) := by
  let D (k : ℕ) := (hd k).toLp (d k)
  let V (k : ℕ) := (hv k).toLp (v k)
  let A := ha.toLp a
  let B := hb.toLp b
  have hD : Tendsto D atTop (𝓝 A) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' d hd a ha).mpr hda
  have hV : Tendsto V atTop (𝓝 B) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv b hb).mpr hvb
  have h := dual_pairing_integral_tendsto μ D V A B hD hV
  have heq (k : ℕ) : (∫ t, D k t (V k t) ∂μ) = ∫ t, d k t (v k t) ∂μ := by
    apply integral_congr_ae
    filter_upwards [(hd k).coeFn_toLp, (hv k).coeFn_toLp] with t ht hv
    exact congrArg₂ (fun (x : E →L[ℝ] ℝ) (y : E) => x y) ht hv
  have heq₀ : (∫ t, A t (B t) ∂μ) = ∫ t, a t (b t) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with t ht hv
    exact congrArg₂ (fun (x : E →L[ℝ] ℝ) (y : E) => x y) ht hv
  simpa only [heq, heq₀] using h

theorem energy_identity_of_function_limits {X E Y : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] (μ : Measure X)
    (d : ℕ → X → (E →L[ℝ] ℝ)) (v : ℕ → X → E)
    (a : X → (E →L[ℝ] ℝ)) (b : X → E)
    (hd : ∀ k, MemLp (d k) 2 μ) (hv : ∀ k, MemLp (v k) 2 μ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hda : Tendsto (fun k => eLpNorm (d k - a) 2 μ) atTop (𝓝 0))
    (hvb : Tendsto (fun k => eLpNorm (v k - b) 2 μ) atTop (𝓝 0))
    (p q : ℕ → Y) (p₀ q₀ : Y) (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto q atTop (𝓝 q₀))
    (he : ∀ k, (1 / 2 : ℝ) * ‖p k‖ ^ 2 - (1 / 2 : ℝ) * ‖q k‖ ^ 2 =
      ∫ t, d k t (v k t) ∂μ) :
    (1 / 2 : ℝ) * ‖p₀‖ ^ 2 - (1 / 2 : ℝ) * ‖q₀‖ ^ 2 = ∫ t, a t (b t) ∂μ := by
  have hl := (hp.norm.pow 2).const_mul (1 / 2 : ℝ) |>.sub
    ((hq.norm.pow 2).const_mul (1 / 2 : ℝ))
  have hr := dual_pairing_integral_tendsto_functions μ d v a b hd hv ha hb hda hvb
  exact tendsto_nhds_unique hl (by simpa only [he] using hr)

/-- The scalar Taylor estimate behind the L² Fréchet derivative of positive
energy. It is valid across the truncation level as well as away from it. -/
theorem scalar_positive_energy_remainder (a b : ℝ) :
    |(1 / 2 : ℝ) * (max b 0) ^ 2 - (1 / 2 : ℝ) * (max a 0) ^ 2 -
      max a 0 * (b - a)| ≤ (1 / 2 : ℝ) * (b - a) ^ 2 := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [max_eq_left ha, max_eq_left hb, abs_le]
    constructor <;> nlinarith [sq_nonneg (b - a)]
  · rw [max_eq_left ha, max_eq_right hb, abs_le]
    have hab : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hb
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · rw [max_eq_right ha, max_eq_left hb, abs_le]
    have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hb
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · rw [max_eq_right ha, max_eq_right hb]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg (b - a))

section PositiveEnergy
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Positive energy on the actual L² quotient. -/
def positiveEnergy (u : MeasureTheory.Lp ℝ 2 μ) : ℝ :=
  (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart u‖ ^ 2

theorem norm_sq_eq_integral_sq (u : MeasureTheory.Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem positiveEnergy_eq_integral (u : MeasureTheory.Lp ℝ 2 μ) :
    positiveEnergy u = ∫ x, (1 / 2 : ℝ) * (max (u x) 0) ^ 2 ∂μ := by
  rw [positiveEnergy, norm_sq_eq_integral_sq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.Lp.coeFn_posPart u] with x hx
  rw [hx]

/-- Integrating the scalar Taylor estimate gives a quadratic remainder in
the full L² increment, hence the Fréchet derivative has no sign restriction. -/
theorem positiveEnergy_remainder (a b : MeasureTheory.Lp ℝ 2 μ) :
    ‖positiveEnergy b - positiveEnergy a -
      inner ℝ (MeasureTheory.Lp.posPart a) (b - a)‖ ≤ (1 / 2 : ℝ) * ‖b - a‖ ^ 2 := by
  have hIa : Integrable (fun x => (1 / 2 : ℝ) * (max (a x) 0) ^ 2) μ :=
    (MeasureTheory.Lp.memLp a).pos_part.integrable_sq.const_mul _
  have hIb : Integrable (fun x => (1 / 2 : ℝ) * (max (b x) 0) ^ 2) μ :=
    (MeasureTheory.Lp.memLp b).pos_part.integrable_sq.const_mul _
  have hIp : Integrable (fun x => max (a x) 0 * (b x - a x)) μ := by
    have h := L2.integrable_inner (𝕜 := ℝ) (MeasureTheory.Lp.posPart a) (b - a)
    apply h.congr
    filter_upwards [MeasureTheory.Lp.coeFn_posPart a, MeasureTheory.Lp.coeFn_sub b a]
      with x hx hs
    simp only [hx, hs, Pi.sub_apply, RCLike.inner_apply, conj_trivial]
    ring
  let R : X → ℝ := fun x => (1 / 2 : ℝ) * (max (b x) 0) ^ 2 -
    (1 / 2 : ℝ) * (max (a x) 0) ^ 2 - max (a x) 0 * (b x - a x)
  have hIR : Integrable R μ := (hIb.sub hIa).sub hIp
  have hinner : inner ℝ (MeasureTheory.Lp.posPart a) (b - a) =
      ∫ x, max (a x) 0 * (b x - a x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_posPart a, MeasureTheory.Lp.coeFn_sub b a]
      with x hx hs
    simp only [hx, hs, Pi.sub_apply, RCLike.inner_apply, conj_trivial]
    ring
  have hEq : positiveEnergy b - positiveEnergy a -
      inner ℝ (MeasureTheory.Lp.posPart a) (b - a) = ∫ x, R x ∂μ := by
    rw [positiveEnergy_eq_integral, positiveEnergy_eq_integral, hinner]
    symm
    calc
      (∫ x, R x ∂μ) =
          (∫ x, (1 / 2 : ℝ) * (max (b x) 0) ^ 2 -
            (1 / 2 : ℝ) * (max (a x) 0) ^ 2 ∂μ) -
          ∫ x, max (a x) 0 * (b x - a x) ∂μ :=
        integral_sub (hIb.sub hIa) hIp
      _ = _ := congrArg (fun z : ℝ => z - ∫ x, max (a x) 0 * (b x - a x) ∂μ)
        (integral_sub hIb hIa)
  rw [hEq]
  calc
    ‖∫ x, R x ∂μ‖ ≤ ∫ x, ‖R x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (1 / 2 : ℝ) * ((b - a) x) ^ 2 ∂μ := by
      apply integral_mono_ae hIR.norm ((MeasureTheory.Lp.memLp (b - a)).integrable_sq.const_mul _)
      filter_upwards [MeasureTheory.Lp.coeFn_sub b a] with x hs
      simp only [R, Real.norm_eq_abs, hs, Pi.sub_apply]
      exact scalar_positive_energy_remainder (a x) (b x)
    _ = (1 / 2 : ℝ) * ‖b - a‖ ^ 2 := by
      rw [integral_const_mul, norm_sq_eq_integral_sq]

/-- The derivative of positive energy is the genuine L² pairing with the
positive part; the estimate holds at functions with a zero level set too. -/
theorem positiveEnergy_hasFDerivAt (a : MeasureTheory.Lp ℝ 2 μ) :
    HasFDerivAt positiveEnergy (innerSL ℝ (MeasureTheory.Lp.posPart a)) a := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero (fun b => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · intro b
    calc
      ‖b - a‖⁻¹ * ‖positiveEnergy b - positiveEnergy a -
          (innerSL ℝ (MeasureTheory.Lp.posPart a)) (b - a)‖ ≤
          ‖b - a‖⁻¹ * ((1 / 2 : ℝ) * ‖b - a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (positiveEnergy_remainder a b) (inv_nonneg.mpr (norm_nonneg _))
      _ = (1 / 2 : ℝ) * ‖b - a‖ := by
        by_cases hz : ‖b - a‖ = 0
        · simp [hz]
        · field_simp
  · have h := ((continuous_id.sub (continuous_const (y := a))).norm.tendsto a).const_mul (1 / 2 : ℝ)
    simpa only [Pi.sub_apply, id_eq, sub_self, norm_zero, mul_zero] using h

/-- The classical time chain identity on L², before regularizing an energy
trajectory. Both endpoint values are the given smooth curve. -/
theorem smooth_positive_energy_identity (F : ℝ → MeasureTheory.Lp ℝ 2 μ)
    (hF : ContDiff ℝ 1 F) (s t : ℝ) :
    positiveEnergy (F t) - positiveEnergy (F s) =
      ∫ r in s..t, inner ℝ (MeasureTheory.Lp.posPart (F r)) (deriv F r) := by
  have hdc : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hpc : Continuous (fun r => MeasureTheory.Lp.posPart (F r)) :=
    MeasureTheory.Lp.continuous_posPart.comp hF.continuous
  have hc : Continuous (fun r => inner ℝ (MeasureTheory.Lp.posPart (F r)) (deriv F r)) :=
    hpc.inner hdc
  have hd (r : ℝ) : HasDerivAt (fun r => positiveEnergy (F r))
      (inner ℝ (MeasureTheory.Lp.posPart (F r)) (deriv F r)) r :=
    (positiveEnergy_hasFDerivAt (F r)).comp_hasDerivAt r
      ((hF.differentiable (by norm_num)) r).hasDerivAt
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (hc.intervalIntegrable s t)).symm

end PositiveEnergy

/-- For a smooth bulk trajectory with nonpositive trace, the classical
L² derivative is exactly the H⁻¹,H¹₀ pairing. This is the identity to apply
to a sign-preserving time regularization of the original trajectory. -/
theorem smooth_ordered_trace_identity {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) (htr : P201Specs.Trace.AgreesWithSmooth tr)
    (F : ℝ → H ℝ Ω 1) (hF : ContDiff ℝ 1 F) (s t : ℝ)
    (hsign : ∀ r ∈ uIcc s t, ∀ᵐ x ∂boundaryMeasure Ω,
      P201Specs.Trace.inclusion Ω hΩ (tr (F r)) x ≤ 0) :
    positiveEnergy (hUnderlying Ω 1 (F t)) - positiveEnergy (hUnderlying Ω 1 (F s)) =
      ∫ r in s..t, pivot Ω (hUnderlying Ω 1 (deriv F r)) (zeroPositive Ω (F r)) := by
  let G : ℝ → Lp ℝ Ω 2 := fun r => hUnderlying Ω 1 (F r)
  have hG : ContDiff ℝ 1 G := (hUnderlying (𝕜 := ℝ) Ω 1).contDiff.comp hF
  have hdG (r : ℝ) : deriv G r = hUnderlying Ω 1 (deriv F r) :=
    ((hUnderlying (𝕜 := ℝ) Ω 1).hasFDerivAt.comp_hasDerivAt r
      ((hF.differentiable (by norm_num)) r).hasDerivAt).deriv
  have he := smooth_positive_energy_identity G hG s t
  refine he.trans (intervalIntegral.integral_congr_ae ?_)
  filter_upwards [] with r hr
  have hv : hZeroUnderlying Ω (zeroPositive Ω (F r)) =
      MeasureTheory.Lp.posPart (G r) := by
    change hUnderlying Ω 1 (zeroPositive Ω (F r)).val = _
    rw [zeroPositive_val Ω hΩ tr htr (F r) (hsign r (uIoc_subset_uIcc hr)), Truncation.underlying_positiveLp]
    exact (positiveL2_eq Ω (G r)).symm
  rw [hdG r]
  change inner ℝ (MeasureTheory.Lp.posPart (G r)) (hUnderlying Ω 1 (deriv F r)) =
    inner ℝ (hUnderlying Ω 1 (deriv F r)) (hZeroUnderlying Ω (zeroPositive Ω (F r)))
  rw [hv, real_inner_comm]

/-- A continuous scalar energy with an integrable interior derivative has
its interval identity at both endpoints too. -/
theorem endpoint_identity_of_interior {T : ℝ} (hT : 0 < T) (E f : ℝ → ℝ)
    (hE : ContinuousOn E (Icc 0 T)) (hf : IntegrableOn f (Ioo 0 T))
    (hi : ∀ s t : ℝ, 0 < s → s < t → t < T → E t - E s = ∫ r in s..t, f r) :
    ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → E t - E s = ∫ r in s..t, f r := by
  have hfcc : IntegrableOn f (Icc 0 T) := by
    simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Icc] using hf
  have hint (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
      IntervalIntegrable f volume s t :=
    (hfcc.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
  let c : ℝ := T / 2
  have hc : c ∈ Ioo 0 T := by dsimp [c]; constructor <;> linarith
  have hiall (s t : ℝ) (hs : s ∈ Ioo 0 T) (ht : t ∈ Ioo 0 T) :
      E t - E s = ∫ r in s..t, f r := by
    rcases lt_trichotomy s t with hst | hst | hst
    · exact hi s t hs.1 hst ht.2
    · subst t; simp
    · have h := hi t s ht.1 hst hs.2
      rw [intervalIntegral.integral_symm]
      linarith
  have heq : EqOn E (fun t => E c + ∫ r in c..t, f r) (Ioo 0 T) := by
    intro t ht
    have h := hiall c t hc ht
    linarith
  have hcont : ContinuousOn (fun t => E c + ∫ r in c..t, f r) (Icc 0 T) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hT.le] using
      intervalIntegral.continuousOn_primitive_interval' (hint 0 T ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩)
        (show c ∈ uIcc 0 T by simpa only [uIcc_of_le hT.le] using Ioo_subset_Icc_self hc)
  have heqcc : EqOn E (fun t => E c + ∫ r in c..t, f r) (Icc 0 T) :=
    heq.of_subset_closure hE hcont Ioo_subset_Icc_self (by rw [closure_Ioo hT.ne])
  intro s t hs ht
  rw [heqcc hs, heqcc ht, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (hint c t (Ioo_subset_Icc_self hc) ht)
    (hint c s (Ioo_subset_Icc_self hc) hs)

/-- The strong-limit and endpoint argument, applied to a local
time regularization, establishes the full theorem. -/
theorem chain_rule_of_regularization : P201Specs.OrderedTraceChain.AssemblyStatement := by
  intro hreg
  refine ⟨membership, ?_⟩
  intro m Ω hΩ tr htr T hT w du U hw hdu hU hrep hd hsign
  letI hnormed : NormedSpace ℝ (H10 ℝ Ω) := inferInstanceAs
    (NormedSpace ℝ ↥(P201Specs.hZeroSubmodule ℝ Ω))
  let ν : Measure ℝ := P201Specs.OrderedTraceChain.timeMeasure T
  let v : ℝ → H10 ℝ Ω := fun r => zeroPositive Ω (w r)
  have hmem := membership Ω hΩ tr htr T w du U hw hdu hU hrep hsign
  have hpair : IntegrableOn (fun r => du r (v r)) (Ioo 0 T) := hmem.2.2.2.2
  let E : ℝ → ℝ := fun r => positiveEnergy (U r)
  have hE : ContinuousOn E (Icc 0 T) := by
    exact continuousOn_const.mul ((positiveL2_continuousOn Ω hU).norm.pow 2)
  have hinterior (s t : ℝ) (hs : 0 < s) (hst : s < t) (ht : t < T) :
      E t - E s = ∫ r in s..t, du r (v r) := by
    let μ : Measure ℝ := volume.restrict (Ioc s t)
    have hμν : μ ≤ ν := Measure.restrict_mono_set volume (by
      intro r hr
      exact ⟨hs.trans hr.1, hr.2.trans_lt ht⟩)
    have hwμ : MemLp w 2 μ := hw.mono_measure hμν
    have hdμ : MemLp du 2 μ := hdu.mono_measure hμν
    have hvμ : MemLp v 2 μ := zeroPositive_memLp Ω hwμ
    obtain ⟨F, hF, hsignF, hMF, hMD, hlimF, hlimD, hlimU⟩ :=
      hreg Ω hΩ tr htr T hT w du U hw hdu hU hrep hd hsign s t hs hst ht
    let d (k : ℕ) : ℝ → Hminus1 ℝ Ω :=
      fun r => pivot Ω (hUnderlying Ω 1 (deriv (F k) r))
    let V (k : ℕ) : ℝ → H10 ℝ Ω := fun r => zeroPositive Ω (F k r)
    have hMV (k) : MemLp (V k) 2 μ := zeroPositive_memLp Ω (hMF k)
    have hlimV : Tendsto (fun k => eLpNorm (V k - v) 2 μ) atTop (𝓝 0) :=
      continuous_comp_tendsto_L2 (zeroPositive Ω) (zeroPositive_continuous Ω)
        (zeroPositive_norm_le Ω) F w hMF hwμ hlimF
    have hident (k : ℕ) :
        (1 / 2 : ℝ) * ‖positiveL2 Ω (hUnderlying Ω 1 (F k t))‖ ^ 2 -
          (1 / 2 : ℝ) * ‖positiveL2 Ω (hUnderlying Ω 1 (F k s))‖ ^ 2 =
          ∫ r, d k r (V k r) ∂μ := by
      have he := smooth_ordered_trace_identity Ω hΩ tr htr (F k) (hF k) s t
        (fun r hr => hsignF k r (by simpa only [uIcc_of_le hst.le] using hr))
      conv_rhs at he => rw [intervalIntegral.integral_of_le hst.le]
      exact he
    have hlimP := ((positiveL2_lipschitz Ω).continuous.tendsto (U t)).comp
      (hlimU t ⟨hst.le, le_rfl⟩)
    have hlimQ := ((positiveL2_lipschitz Ω).continuous.tendsto (U s)).comp
      (hlimU s ⟨le_rfl, hst.le⟩)
    have he := @energy_identity_of_function_limits ℝ
      ↥(P201Specs.hZeroSubmodule ℝ Ω) (Lp ℝ Ω 2) _ _ hnormed _ μ d V du v hMD hMV hdμ hvμ
      hlimD hlimV _ _ _ _ hlimP hlimQ hident
    conv_rhs => rw [intervalIntegral.integral_of_le hst.le]
    exact he
  intro s t hs hst ht
  have he := endpoint_identity_of_interior hT E (fun r => du r (v r)) hE hpair hinterior
    s t ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩
  conv_rhs at he => rw [intervalIntegral.integral_of_le hst]
  exact he


section Mollification
open Function Metric ContinuousLinearMap
open scoped Convolution
namespace TimeMollifier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


/-- The Lp translation error for Banach-valued functions tends to zero. -/
theorem translation_error_tendsto (f : ℝ → E) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) (hf : MemLp f p volume) :
    Tendsto (fun y => eLpNorm (fun x => f (x-y) - f x) p volume)
      (𝓝 0) (𝓝 0) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let v := hf.toLp f
  let shift (r : ℝ) : C(ℝ, ℝ) := ⟨fun t => t-r, continuous_id.sub continuous_const⟩
  have hshift : Continuous shift :=
    ContinuousMap.continuous_of_continuous_uncurry shift (continuous_snd.sub continuous_fst)
  have hmp (r : ℝ) : MeasurePreserving (shift r) volume volume :=
    measurePreserving_sub_right volume r
  let translate (r : ℝ) := Lp.compMeasurePreserving (shift r) (hmp r) v
  have hc : Continuous translate :=
    (continuous_const : Continuous (fun _ : ℝ => v)).compMeasurePreservingLp hshift hmp hpt
  have heq (y : ℝ) : eLpNorm (fun x => f (x-y) - f x) p volume =
      ENNReal.ofReal ‖translate y - v‖ := by
    rw [ofReal_norm, Lp.enorm_def]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (translate y) v,
      Lp.coeFn_compMeasurePreserving v (hmp y),
      (hmp y).quasiMeasurePreserving.ae hf.coeFn_toLp,
      hf.coeFn_toLp] with x hsub ht hs hv
    simp only [Pi.sub_apply] at hsub
    rw [hsub]
    change (translate y) x = v (x-y) at ht
    change v (x-y) = f (x-y) at hs
    change v x = f x at hv
    rw [ht, hs, hv]
  have hzero : translate 0 = v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving v (hmp 0)] with x hx
    simpa [translate, shift] using hx
  have htn : Tendsto (fun y => ‖translate y - v‖) (𝓝 0) (𝓝 0) := by
    simpa only [Pi.sub_apply, hzero, sub_self, norm_zero] using
      ((hc.sub (continuous_const (y := v))).norm.tendsto 0)
  have ht : Tendsto (fun y => ENNReal.ofReal ‖translate y - v‖) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp htn
  exact ht.congr' (Eventually.of_forall fun y => (heq y).symm)

/-- Reduce the Banach-valued convolution error to scalar Minkowski. -/
theorem convolution_error_bound
    (f : ℝ → E) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hfm : StronglyMeasurable f) (hf : MemLp f p volume)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hφn : ∀ y, 0 ≤ φ y) (hφmass : ∫ y, φ y = 1)
    (η : ℝ≥0∞) (hη : η ≠ ∞)
    (hcontrol : ∀ y ∈ support φ,
      eLpNorm (fun x => f (x-y) - f x) p volume ≤ η) :
    eLpNorm ((φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) p volume ≤ η := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  let F : ℝ × ℝ → E := fun z => φ z.2 • (f (z.1-z.2) - f z.1)
  have hF : StronglyMeasurable F := (hφ.stronglyMeasurable.comp_measurable measurable_snd).smul
    ((hfm.comp_measurable (measurable_fst.sub measurable_snd)).sub
      (hfm.comp_measurable measurable_fst))
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hcφ
  have hconv (x : ℝ) : Integrable (fun y => φ y • f (x-y)) :=
    hcφ.convolutionExists_left L hφ (hf.locallyIntegrable hp) x
  have hconst (x : ℝ) : Integrable (fun y => φ y • f x) := hφi.smul_const (f x)
  have heq (x : ℝ) : (∫ y, F (x,y)) = (φ ⋆[L, volume] f) x - f x := by
    simp only [F, smul_sub, integral_sub (hconv x) (hconst x),
      integral_smul_const, hφmass, one_smul, convolution, L, ContinuousLinearMap.lsmul_apply]
  have hs (y : ℝ) : eLpNorm (fun x => ‖F (x,y)‖) p volume ≤ ‖φ y‖ₑ * η := by
    have hFy : AEStronglyMeasurable (fun x => F (x,y)) volume :=
      (hF.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    rw [eLpNorm_norm _ hFy]
    change eLpNorm ((φ y) • (fun x => f (x-y) - f x)) p volume ≤ _
    rw [eLpNorm_const_smul]
    by_cases hy : y ∈ support φ
    · gcongr
      exact hcontrol y hy
    · simp [notMem_support.mp hy]
  have hmass : (∫⁻ y, ‖φ y‖ₑ) = 1 := by
    simp_rw [← ofReal_norm, Real.norm_of_nonneg (hφn _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hφi (Eventually.of_forall hφn), hφmass]
    simp
  have hbound : (∫⁻ y, eLpNorm (fun x => ‖F (x,y)‖) p volume) ≤ η := by
    calc
      _ ≤ ∫⁻ y, ‖φ y‖ₑ * η := lintegral_mono hs
      _ = η := by rw [lintegral_mul_const _ hφ.measurable.enorm, hmass, one_mul]
  obtain ⟨hi, hb⟩ := ExpandedFA.Distributions.minkowski_integral_eLpNorm
    volume volume p hp hpt (fun z => ‖F z‖) hF.norm.measurable
    (hbound.trans_lt (lt_top_iff_ne_top.mpr hη))
  apply le_trans _ (hb.trans hbound)
  apply eLpNorm_mono_real ((hφ.aestronglyMeasurable.convolution L hf.aestronglyMeasurable).sub
    hf.aestronglyMeasurable)
  intro x
  change ‖(φ ⋆[L, volume] f) x - f x‖ ≤ _
  rw [← heq]
  exact norm_integral_le_integral_norm _


/-- A shrinking family of normalized bumps approximates a Banach-valued Lp function. -/
theorem bump_eLpNorm_tendsto_of_stronglyMeasurable {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : ℝ → E) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hfm : StronglyMeasurable f) (hf : MemLp f p volume) :
    Tendsto (fun i => eLpNorm
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) p volume)
      l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  by_cases hηt : η = ∞
  · simp [hηt]
  have ht := ENNReal.tendsto_nhds_zero.mp (translation_error_tendsto f hp hpt hf) η hη
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hsmall : ∀ᶠ i in l, (φ i).rOut < r := hφ.eventually (gt_mem_nhds hr)
  filter_upwards [hsmall] with i hi
  apply convolution_error_bound f hp hpt hfm hf ((φ i).normed volume)
    ((φ i).contDiff_normed (n := ⊤)).continuous ((φ i).hasCompactSupport_normed)
    ((φ i).nonneg_normed) ((φ i).integral_normed) η hηt
  intro y hy
  apply hball
  rw [(φ i).support_normed_eq] at hy
  exact ball_subset_ball hi.le hy

/-- No separability assumption on the Banach codomain is needed: choose a strongly
measurable representative and use representative independence of convolution. -/
theorem bump_eLpNorm_tendsto {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : ℝ → E) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hf : MemLp f p volume) :
    Tendsto (fun i => eLpNorm
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) p volume)
      l (𝓝 0) := by
  let f' := hf.aestronglyMeasurable.mk f
  have hff : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hfm : StronglyMeasurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have ht := bump_eLpNorm_tendsto_of_stronglyMeasurable hφ f' hp hpt hfm (hf.ae_eq hff)
  convert ht using 1
  ext i
  apply eLpNorm_congr_ae
  have hc : ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) =
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hff
  exact (EventuallyEq.of_eq hc).sub hff


/-- Zero extension converts restricted MemLp into global MemLp. -/
theorem zeroExtend_memLp {S : Set ℝ} (hS : MeasurableSet S)
    (f : ℝ → E) {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict S)) :
    MemLp (S.indicator f) p volume :=
  (memLp_indicator_iff_restrict hS.nullMeasurableSet).2 hf

/-- Global approximate-identity convergence restricts to every measurable interior set,
where the zero extension agrees with the original function. -/
theorem bump_local_eLpNorm_tendsto {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {S R : Set ℝ} (hS : MeasurableSet S) (hRS : R ⊆ S)
    (f : ℝ → E) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hf : MemLp f p (volume.restrict S)) :
    Tendsto (fun i => eLpNorm
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator f) - f)
        p (volume.restrict R)) l (𝓝 0) := by
  have hz := zeroExtend_memLp hS f hf
  have ht := bump_eLpNorm_tendsto hφ (S.indicator f) hp hpt hz
  have heq : S.indicator f =ᵐ[volume.restrict R] f :=
    ae_restrict_of_ae_restrict_of_subset hRS (indicator_ae_eq_restrict hS.nullMeasurableSet)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht η hη] with i hi
  have he : eLpNorm
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator f) -
        S.indicator f) p (volume.restrict R) =
      eLpNorm
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator f) - f)
        p (volume.restrict R) :=
    eLpNorm_congr_ae (EventuallyEq.rfl.sub heq)
  rw [← he]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hi

/-- The form used on compact interior time intervals in the ordered-trace proof. -/
theorem bump_interval_eLpNorm_tendsto {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (T a b : ℝ) (ha : 0 < a) (hb : b < T)
    (f : ℝ → E) (hf : MemLp f 2 (volume.restrict (Ioo 0 T))) :
    Tendsto (fun i => eLpNorm
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (Ioo 0 T).indicator f) - f) 2 (volume.restrict (Ioc a b))) l (𝓝 0) := by
  apply bump_local_eLpNorm_tendsto hφ measurableSet_Ioo (fun x hx => ?_) f
    (by norm_num) (by norm_num) hf
  exact ⟨lt_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩


/-- Kernels supported in a fixed allowed time radius, shrinking to zero. -/
def shrinkingBump (δ : ℝ) (hδ : 0 < δ) (k : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (δ / ((k : ℝ) + 2)) / 2
  rOut := δ / ((k : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

@[simp] theorem shrinkingBump_rOut (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    (shrinkingBump δ hδ k).rOut = δ / ((k : ℝ) + 2) := rfl

theorem shrinkingBump_rOut_lt (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    (shrinkingBump δ hδ k).rOut < δ := by
  change δ / ((k : ℝ) + 2) < δ
  exact div_lt_self hδ (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)

theorem shrinkingBump_rOut_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun k => (shrinkingBump δ hδ k).rOut) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => δ / ((k : ℝ) + 2)) atTop (𝓝 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_const_div_atTop_nhds_zero_nat δ).comp (tendsto_add_atTop_nat 2)


end TimeMollifier

end Mollification

section TraceCone
open Function Metric ContinuousLinearMap
open scoped Convolution

theorem realLp_orderedModule {α : Type*} [MeasurableSpace α]
    (p : ℝ≥0∞) (μ : Measure α) : IsOrderedModule ℝ (MeasureTheory.Lp ℝ p μ) := by
  apply IsOrderedModule.of_smul_nonneg
  intro c hc u hu
  apply (MeasureTheory.Lp.coeFn_nonneg _).mp
  have hu' := (MeasureTheory.Lp.coeFn_nonneg u).mpr hu
  filter_upwards [MeasureTheory.Lp.coeFn_smul c u, hu'] with x hx hux
  simpa only [hx, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using mul_nonneg hc hux

local instance {α : Type*} [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    IsOrderedModule ℝ (MeasureTheory.Lp ℝ p μ) := realLp_orderedModule p μ

theorem realLp_coeFn_nonpos {α : Type*} [MeasurableSpace α]
    {p : ℝ≥0∞} {μ : Measure α} (u : MeasureTheory.Lp ℝ p μ) :
    (∀ᵐ x ∂μ, u x ≤ 0) ↔ u ≤ 0 := by
  constructor
  · intro hu
    apply (MeasureTheory.Lp.coeFn_le _ _).mp
    filter_upwards [hu, MeasureTheory.Lp.coeFn_zero ℝ p μ] with x hx hz
    simpa only [hz, Pi.zero_apply] using hx
  · intro hu
    have hh := (MeasureTheory.Lp.coeFn_le _ _).mpr hu
    filter_upwards [hh, MeasureTheory.Lp.coeFn_zero ℝ p μ] with x hx hz
    simpa only [hz, Pi.zero_apply] using hx

def negativeTraceCone {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) :
    Set (H ℝ Ω 1) :=
  {u | ∀ᵐ x ∂boundaryMeasure Ω, P201Specs.Trace.inclusion Ω hΩ (tr u) x ≤ 0}

theorem negativeTraceCone_eq {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) :
    negativeTraceCone Ω hΩ tr =
      ((P201Specs.Trace.inclusion Ω hΩ).comp tr) ⁻¹' Iic 0 := by
  ext u
  exact realLp_coeFn_nonpos _

theorem negativeTraceCone_closed {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) :
    IsClosed (negativeTraceCone Ω hΩ tr) := by
  rw [negativeTraceCone_eq]
  exact isClosed_Iic.preimage ((P201Specs.Trace.inclusion Ω hΩ).comp tr).continuous

theorem negativeTraceCone_convex {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) :
    Convex ℝ (negativeTraceCone Ω hΩ tr) := by
  rw [negativeTraceCone_eq]
  exact (convex_Iic (0 : P201Specs.Trace.BoundaryL2 Ω)).linear_preimage
    ((P201Specs.Trace.inclusion Ω hΩ).comp tr).toLinearMap

theorem negativeTraceCone_zero {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) :
    (0 : H ℝ Ω 1) ∈ negativeTraceCone Ω hΩ tr := by
  rw [negativeTraceCone_eq]
  simp

theorem negativeTraceCone_smul {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ)
    {u : H ℝ Ω 1} (hu : u ∈ negativeTraceCone Ω hΩ tr)
    {c : ℝ} (hc : 0 ≤ c) : c • u ∈ negativeTraceCone Ω hΩ tr := by
  rw [negativeTraceCone_eq] at hu ⊢
  change ((P201Specs.Trace.inclusion Ω hΩ).comp tr) u ≤ 0 at hu
  change ((P201Specs.Trace.inclusion Ω hΩ).comp tr) (c • u) ≤ 0
  simpa only [map_smul, smul_zero] using smul_le_smul_of_nonneg_left hu hc

theorem integral_mem_negativeTraceCone {α : Type*} [MeasurableSpace α]
    {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) {μ : Measure α} {f : α → H ℝ Ω 1}
    (hf : Integrable f μ) (hsign : ∀ᵐ t ∂μ, f t ∈ negativeTraceCone Ω hΩ tr) :
    (∫ t, f t ∂μ) ∈ negativeTraceCone Ω hΩ tr := by
  rw [negativeTraceCone_eq] at hsign ⊢
  change ((P201Specs.Trace.inclusion Ω hΩ).comp tr) (∫ t, f t ∂μ) ≤ 0
  rw [← ContinuousLinearMap.integral_comp_comm _ hf]
  exact integral_nonpos_of_ae hsign


theorem integral_smul_mem_negativeTraceCone {α : Type*} [MeasurableSpace α]
    {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) {μ : Measure α}
    {f : α → H ℝ Ω 1} {κ : α → ℝ}
    (hint : Integrable (fun s => κ s • f s) μ)
    (hκ : ∀ᵐ s ∂μ, 0 ≤ κ s)
    (hf : ∀ᵐ s ∂μ, f s ∈ negativeTraceCone Ω hΩ tr) :
    (∫ s, κ s • f s ∂μ) ∈ negativeTraceCone Ω hΩ tr := by
  apply integral_mem_negativeTraceCone Ω hΩ tr hint
  filter_upwards [hκ, hf] with s hsκ hsf
  exact negativeTraceCone_smul Ω hΩ tr hsf hsκ

theorem indicator_mem_negativeTraceCone_ae {α : Type*} [MeasurableSpace α]
    {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) {μ : Measure α}
    {f : α → H ℝ Ω 1} {S : Set α} (hS : MeasurableSet S)
    (hf : ∀ᵐ s ∂μ.restrict S, f s ∈ negativeTraceCone Ω hΩ tr) :
    ∀ᵐ s ∂μ, S.indicator f s ∈ negativeTraceCone Ω hΩ tr := by
  rw [ae_restrict_iff' hS] at hf
  filter_upwards [hf] with s hs
  by_cases hsS : s ∈ S
  · simpa only [Set.indicator_of_mem hsS] using hs hsS
  · simpa only [Set.indicator_of_notMem hsS] using negativeTraceCone_zero Ω hΩ tr

theorem time_convolution_mem_negativeTraceCone {m : ℕ}
    (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ)
    {f : ℝ → H ℝ Ω 1} {κ : ℝ → ℝ}
    (hκ : ∀ᵐ s ∂volume, 0 ≤ κ s)
    (hf : ∀ᵐ s ∂volume, f s ∈ negativeTraceCone Ω hΩ tr)
    (r : ℝ) (hint : Integrable (fun s => κ s • f (r - s))) :
    (∫ s, κ s • f (r - s)) ∈ negativeTraceCone Ω hΩ tr := by
  apply integral_smul_mem_negativeTraceCone Ω hΩ tr hint hκ
  exact (volume.measurePreserving_sub_left r).quasiMeasurePreserving.ae hf


end TraceCone

section ConvolutionEndpoints
open Function Metric ContinuousLinearMap
open scoped Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem linearMap_zeroExtension_ae (L : E →L[ℝ] F) {f : ℝ → E} {U : ℝ → F}
    {T : ℝ} (hrep : ∀ᵐ t ∂volume.restrict (Ioo 0 T), U t = L (f t)) :
    (fun t => L ((Ioo 0 T).indicator f t)) =ᵐ[volume] (Ioo 0 T).indicator U := by
  rw [ae_restrict_iff' measurableSet_Ioo] at hrep
  filter_upwards [hrep] with t ht
  by_cases htS : t ∈ Ioo 0 T
  · simpa only [indicator_of_mem htS] using (ht htS).symm
  · simp only [indicator_of_notMem htS, map_zero]

theorem linearMap_bump_convolution_eq (L : E →L[ℝ] F)
    {f : ℝ → E} {U : ℝ → F} {T : ℝ}
    (hf : IntegrableOn f (Ioo 0 T))
    (hrep : ∀ᵐ t ∂volume.restrict (Ioo 0 T), U t = L (f t))
    (φ : ContDiffBump (0 : ℝ)) (r : ℝ) :
    L ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] (Ioo 0 T).indicator f) r) =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (Ioo 0 T).indicator U) r := by
  have hfext : Integrable ((Ioo 0 T).indicator f) := hf.integrable_indicator measurableSet_Ioo
  have hint := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hfext.locallyIntegrable r
  change Integrable (fun t => φ.normed volume t • (Ioo 0 T).indicator f (r - t)) at hint
  rw [convolution_lsmul, convolution_lsmul, ← L.integral_comp_comm hint]
  apply integral_congr_ae
  have hrep' := (volume.measurePreserving_sub_left r).quasiMeasurePreserving.ae
    (linearMap_zeroExtension_ae L hrep)
  filter_upwards [hrep'] with s hs
  simp only [map_smul, hs]

theorem linearMap_bump_convolution_tendsto (L : E →L[ℝ] F)
    {f : ℝ → E} {U : ℝ → F} {T : ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo 0 T)))
    (hU : ContinuousOn U (Icc 0 T))
    (hrep : ∀ᵐ t ∂volume.restrict (Ioo 0 T), U t = L (f t))
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0))
    {r : ℝ} (hr : r ∈ Ioo 0 T) :
    Tendsto (fun k => L (((φ k).normed volume ⋆[lsmul ℝ ℝ, volume]
      (Ioo 0 T).indicator f) r)) atTop (𝓝 (U r)) := by
  have hfi : IntegrableOn f (Ioo 0 T) := hf.integrable (by norm_num)
  have hfext : Integrable ((Ioo 0 T).indicator f) := hfi.integrable_indicator measurableSet_Ioo
  have hUext : AEStronglyMeasurable ((Ioo 0 T).indicator U) volume :=
    (L.integrable_comp hfext).aestronglyMeasurable.congr (linearMap_zeroExtension_ae L hrep)
  have heq : (Ioo 0 T).indicator U =ᶠ[𝓝 r] U := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact indicator_of_mem ht U
  have hcont : Tendsto ((Ioo 0 T).indicator U) (𝓝 r) (𝓝 (U r)) :=
    (hU.continuousAt (Icc_mem_nhds hr.1 hr.2)).tendsto.congr' heq.symm
  have hlim : Tendsto (fun k => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume]
      (Ioo 0 T).indicator U) r) atTop (𝓝 (U r)) :=
    ContDiffBump.convolution_tendsto_right hφ (Eventually.of_forall fun _ => hUext)
      (hcont.comp tendsto_snd) tendsto_const_nhds
  exact hlim.congr (fun k => (linearMap_bump_convolution_eq L hfi hrep (φ k) r).symm)


end ConvolutionEndpoints

section WeakConvolution
open Function Metric ContinuousLinearMap
open scoped Convolution ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- Time convolution commutes with the specified dual-valued weak derivative. -/
theorem convolution_weak_derivative (J : E →L[ℝ] (V →L[ℝ] ℝ)) (T : ℝ)
    (w : ℝ → E) (du : ℝ → (V →L[ℝ] ℝ))
    (hw : MemLp w 2 (volume.restrict (Ioo 0 T)))
    (hdu : MemLp du 2 (volume.restrict (Ioo 0 T)))
    (hd : ∀ v : V,
      ∀ φ : TestFunction (⟨Ioo 0 T, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) ℝ ⊤,
        (∫ y in Ioo 0 T, deriv φ y * J (w y) v) =
          -(∫ y in Ioo 0 T, φ y * du y v))
    (κ : ℝ → ℝ) (hcκ : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (r : ℝ) (hsκ : tsupport (fun y => κ (r-y)) ⊆ Ioo 0 T) :
    J (deriv (κ ⋆[lsmul ℝ ℝ, volume] ((Ioo 0 T).indicator w)) r) =
      (κ ⋆[lsmul ℝ ℝ, volume] ((Ioo 0 T).indicator du)) r := by
  let w₀ := (Ioo 0 T).indicator w
  let d₀ := (Ioo 0 T).indicator du
  have hw₀ : Integrable w₀ volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hw.integrable (by norm_num))
  have hd₀ : Integrable d₀ volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hdu.integrable (by norm_num))
  have hdF := hcκ.hasDerivAt_convolution_left (lsmul ℝ ℝ)
    (hκ.of_le (by simp)) hw₀.locallyIntegrable r
  rw [hdF.deriv, convolution_eq_swap, convolution_eq_swap]
  let φ : TestFunction (⟨Ioo 0 T, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) ℝ ⊤ :=
    ⟨fun y => κ (r-y), hκ.comp (contDiff_const.sub contDiff_id),
      hcκ.comp_homeomorph (Homeomorph.subLeft r), hsκ⟩
  have hdφ (y : ℝ) : deriv φ y = -deriv κ (r-y) := by
    exact ((hκ.differentiable (by simp)) (r-y)).hasDerivAt.comp y
      ((hasDerivAt_id y).const_sub r) |>.deriv |>.trans (by simp)
  have hIw : Integrable (fun y => deriv κ (r-y) • w₀ y) volume :=
    hw₀.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((hκ.continuous_deriv (by simp)).comp (continuous_const.sub continuous_id))
      ((hcκ.deriv).comp_homeomorph (Homeomorph.subLeft r))
  have hId : Integrable (fun y => κ (r-y) • d₀ y) volume :=
    hd₀.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hκ.continuous.comp (continuous_const.sub continuous_id))
      (hcκ.comp_homeomorph (Homeomorph.subLeft r))
  change J (∫ y, deriv κ (r-y) • w₀ y) = ∫ y, κ (r-y) • d₀ y
  rw [← J.integral_comp_comm hIw]
  apply ContinuousLinearMap.ext
  intro v
  let ev : (V →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  change ev (∫ y, J (deriv κ (r-y) • w₀ y)) =
    ev (∫ y, κ (r-y) • d₀ y)
  rw [← ev.integral_comp_comm (J.integrable_comp hIw), ← ev.integral_comp_comm hId]
  simp only [map_smul, smul_eq_mul]
  have he := hd v φ
  have he' : (∫ y in Ioo 0 T,
      deriv κ (r-y) * J (w y) v) =
        ∫ y in Ioo 0 T, κ (r-y) * du y v := by
    simp only [hdφ, neg_mul, integral_neg] at he
    exact neg_injective he
  have hl : (∫ y, deriv κ (r-y) * ev (J (w₀ y))) =
      ∫ y in Ioo 0 T, deriv κ (r-y) * J (w y) v := by
    have hfun : (fun y => deriv κ (r-y) * ev (J (w₀ y))) =
        (Ioo 0 T).indicator (fun y => deriv κ (r-y) * ev (J (w y))) := by
      ext y
      by_cases hy : y ∈ Ioo 0 T <;> simp [w₀, hy]
    rw [hfun, integral_indicator measurableSet_Ioo]
    rfl
  have hr : (∫ y, κ (r-y) * ev (d₀ y)) = ∫ y in Ioo 0 T, κ (r-y) * du y v := by
    have hfun : (fun y => κ (r-y) * ev (d₀ y)) =
        (Ioo 0 T).indicator (fun y => κ (r-y) * du y v) := by
      ext y
      by_cases hy : y ∈ Ioo 0 T <;> simp [d₀, hy, ev]
    rw [hfun, integral_indicator measurableSet_Ioo]
  exact hl.trans (he'.trans hr.symm)

end WeakConvolution


section LocalRegularization
open Set MeasureTheory Filter ContinuousLinearMap
open scoped ENNReal Topology Convolution ContDiff

theorem continuous_memLp_Ioc {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : Continuous f) (a b : ℝ) :
    MemLp f 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  exact hC r (Ioc_subset_Icc_self hr)

/-- Actual construction by nonnegative compactly supported time convolution. -/
theorem local_regularization :
    P201Specs.OrderedTraceChain.LocalRegularizationStatement := by
  intro m Ω hΩ tr htr T hT w du U hw hdu hU hrep hd hsign a b ha hab hb
  letI hnormed : NormedSpace ℝ (H10 ℝ Ω) := inferInstanceAs
    (NormedSpace ℝ ↥(P201Specs.hZeroSubmodule ℝ Ω))
  letI hdual : NormedAddCommGroup (Hminus1 ℝ Ω) := inferInstanceAs
    (NormedAddCommGroup (↥(P201Specs.hZeroSubmodule ℝ Ω) →L[ℝ] ℝ))
  letI hduals : NormedSpace ℝ (Hminus1 ℝ Ω) := inferInstanceAs
    (NormedSpace ℝ (↥(P201Specs.hZeroSubmodule ℝ Ω) →L[ℝ] ℝ))
  letI hdualc : CompleteSpace (Hminus1 ℝ Ω) := inferInstanceAs
    (CompleteSpace (↥(P201Specs.hZeroSubmodule ℝ Ω) →L[ℝ] ℝ))
  let δ : ℝ := min a (T-b) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (lt_min ha (sub_pos.mpr hb))
  have hδa : δ < a := by
    have hmin : min a (T-b) ≤ a := min_le_left _ _
    dsimp [δ]
    linarith
  have hδb : δ < T-b := by
    have hmin : min a (T-b) ≤ T-b := min_le_right _ _
    dsimp [δ]
    linarith
  let φ : ℕ → ContDiffBump (0 : ℝ) := TimeMollifier.shrinkingBump δ hδ
  let κ : ℕ → ℝ → ℝ := fun k => (φ k).normed volume
  let w₀ : ℝ → H ℝ Ω 1 := (Ioo 0 T).indicator w
  let d₀ : ℝ → Hminus1 ℝ Ω := (Ioo 0 T).indicator du
  let F : ℕ → ℝ → H ℝ Ω 1 := fun k => κ k ⋆[lsmul ℝ ℝ, volume] w₀
  let D : ℕ → ℝ → Hminus1 ℝ Ω := fun k => κ k ⋆[lsmul ℝ ℝ, volume] d₀
  let J : H ℝ Ω 1 →L[ℝ] Hminus1 ℝ Ω := (pivot Ω).comp (hUnderlying Ω 1)
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    TimeMollifier.shrinkingBump_rOut_tendsto δ hδ
  have hwi : IntegrableOn w (Ioo 0 T) := hw.integrable (by norm_num)
  have hw₀ : Integrable w₀ := hwi.integrable_indicator measurableSet_Ioo
  have hdi : IntegrableOn du (Ioo 0 T) := hdu.integrable (by norm_num)
  have hd₀ : Integrable d₀ := hdi.integrable_indicator measurableSet_Ioo
  have hFsmooth (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (F k) :=
    (φ k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ k).contDiff_normed hw₀.locallyIntegrable
  have hsupp (k : ℕ) (r : ℝ) (hr : r ∈ Icc a b) :
      tsupport (fun y => κ k (r-y)) ⊆ Ioo 0 T := by
    intro y hy
    have hy' := tsupport_comp_subset_preimage (κ k)
      (continuous_const.sub continuous_id) hy
    change r-y ∈ tsupport ((φ k).normed volume) at hy'
    rw [(φ k).tsupport_normed_eq] at hy'
    have hnorm : |r-y| ≤ (φ k).rOut := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hy'
    have hφδ : (φ k).rOut < δ := TimeMollifier.shrinkingBump_rOut_lt δ hδ k
    have habs := abs_le.mp hnorm
    constructor <;> linarith [hr.1, hr.2]
  have hdJ : ∀ v : H10 ℝ Ω,
      ∀ ψ : TestFunction (⟨Ioo 0 T, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) ℝ ⊤,
        (∫ y in Ioo 0 T, deriv ψ y * J (w y) v) =
          -(∫ y in Ioo 0 T, ψ y * du y v) := by
    intro v ψ
    calc
      _ = ∫ y in Ioo 0 T, deriv ψ y * inner ℝ (U y) (hZeroUnderlying Ω v) := by
        apply integral_congr_ae
        filter_upwards [hrep] with y hy
        rw [hy]
        rfl
      _ = _ := hd v ψ
  have hdF (k : ℕ) (r : ℝ) (hr : r ∈ Icc a b) :
      J (deriv (F k) r) = D k r := by
    exact @convolution_weak_derivative (H ℝ Ω 1) ↥(P201Specs.hZeroSubmodule ℝ Ω)
      _ _ _ _ hnormed J T w du hw hdu hdJ (κ k)
      (φ k).hasCompactSupport_normed (φ k).contDiff_normed r (hsupp k r hr)
  have hsign₀ : ∀ᵐ r ∂volume, w₀ r ∈ negativeTraceCone Ω hΩ tr :=
    indicator_mem_negativeTraceCone_ae Ω hΩ tr measurableSet_Ioo hsign
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (hFsmooth k).of_le (by simp)
  · intro k r hr
    have hi : Integrable (fun s => κ k s • w₀ (r-s)) :=
      (φ k).hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
        (φ k).continuous_normed hw₀.locallyIntegrable r
    exact time_convolution_mem_negativeTraceCone Ω hΩ tr
      (Eventually.of_forall (φ k).nonneg_normed) hsign₀ r hi
  · intro k
    exact continuous_memLp_Ioc (hFsmooth k).continuous a b
  · intro k
    exact continuous_memLp_Ioc
      (J.continuous.comp ((hFsmooth k).continuous_deriv (by simp))) a b
  · exact TimeMollifier.bump_interval_eLpNorm_tendsto hφ T a b ha hb w hw
  · have hlim := TimeMollifier.bump_interval_eLpNorm_tendsto hφ T a b ha hb du hdu
    apply hlim.congr'
    filter_upwards [] with k
    apply eLpNorm_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    change D k r - du r = J (deriv (F k) r) - du r
    rw [hdF k r (Ioc_subset_Icc_self hr)]
  · intro r hr
    exact linearMap_bump_convolution_tendsto (hUnderlying Ω 1) hw hU hrep φ hφ
      ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩


end LocalRegularization

/-- The ordered-trace positive-part time chain rule on the full closed time interval. -/
theorem full_chain_rule : P201Specs.OrderedTraceChain.FullStatement :=
  chain_rule_of_regularization local_regularization

end P201.OrderedTraceChain
