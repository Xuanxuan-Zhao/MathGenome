import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalHolder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.FractionalIntegrals
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace ExpandedFA.PartV.FractionalHolder
open Spec
open ExpandedFA.PartV.FractionalIntegrals
open ExpandedFA.PartV.FractionalIntegrals.Spec

variable {𝕜 : Type} [RCLike 𝕜]

/-- Bridge from the classical norm inequality to Mathlib's metric definition. -/
lemma holderOnInterval_iff {β T : ℝ} (hβ : 0 ≤ β) (f : ℝ → 𝕜) :
    HolderOnInterval β T f ↔
      ∃ C : ℝ≥0, HolderOnWith C (NNReal.mk β hβ) f (Icc (0 : ℝ) T) := by
  constructor
  · rintro ⟨C, hC, hf⟩
    refine ⟨NNReal.mk C hC, fun x hx y hy => ?_⟩
    simp only [edist_dist, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hβ,
      ← ENNReal.ofReal_eq_coe_nnreal hC, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (hf x hx y hy)
  · rintro ⟨C, hf⟩
    refine ⟨C, C.coe_nonneg, fun x hx y hy => ?_⟩
    have h := hf.dist_le hx hy
    simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using h

lemma holderOnInterval_continuousOn {β T : ℝ} (hβ : 0 < β) {f : ℝ → 𝕜}
    (hf : HolderOnInterval β T f) : ContinuousOn f (Icc (0 : ℝ) T) := by
  obtain ⟨C, hC⟩ := (holderOnInterval_iff hβ.le f).mp hf
  exact hC.continuousOn hβ

lemma holderOnInterval_add {β T : ℝ} {f g : ℝ → 𝕜}
    (hf : HolderOnInterval β T f) (hg : HolderOnInterval β T g) :
    HolderOnInterval β T (f+g) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C+D, add_nonneg hC hD, fun x hx y hy => ?_⟩
  calc
    ‖(f+g) x - (f+g) y‖ = ‖(f x-f y) + (g x-g y)‖ := by
      congr 1; simp only [Pi.add_apply]; abel
    _ ≤ ‖f x-f y‖ + ‖g x-g y‖ := norm_add_le _ _
    _ ≤ C * |x-y| ^ β + D * |x-y| ^ β := add_le_add (hf x hx y hy) (hg x hx y hy)
    _ = (C+D) * |x-y| ^ β := by ring

lemma holderOnInterval_const_smul {β T : ℝ} {f : ℝ → 𝕜}
    (hf : HolderOnInterval β T f) (c : ℝ) :
    HolderOnInterval β T (c • f) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨‖c‖*C, mul_nonneg (norm_nonneg _) hC, fun x hx y hy => ?_⟩
  calc
    ‖(c • f) x - (c • f) y‖ = ‖c‖ * ‖f x-f y‖ := by
      rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul]
    _ ≤ ‖c‖ * (C * |x-y| ^ β) := mul_le_mul_of_nonneg_left (hf x hx y hy) (norm_nonneg _)
    _ = _ := by ring

/-- Products of bounded scalar Hölder functions on a compact interval. -/
lemma holderOnInterval_mul {β T : ℝ} (hβ : 0 < β) {f g : ℝ → 𝕜}
    (hf : HolderOnInterval β T f) (hg : HolderOnInterval β T g) :
    HolderOnInterval β T (f*g) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (holderOnInterval_continuousOn hβ hf)
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (holderOnInterval_continuousOn hβ hg)
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨max M 0 * D + max N 0 * C, by positivity, fun x hx y hy => ?_⟩
  have he : (f*g) x - (f*g) y = f x * (g x-g y) + (f x-f y) * g y := by
    simp only [Pi.mul_apply]; ring
  rw [he]
  calc
    _ ≤ ‖f x * (g x-g y)‖ + ‖(f x-f y) * g y‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x-g y‖ + ‖g y‖ * ‖f x-f y‖ := by rw [norm_mul, norm_mul]; ring
    _ ≤ max M 0 * (D * |x-y| ^ β) + max N 0 * (C * |x-y| ^ β) := by
      gcongr
      · exact (hM x hx).trans (le_max_left _ _)
      · exact hg x hx y hy
      · exact (hN y hy).trans (le_max_left _ _)
      · exact hf x hx y hy
    _ = _ := by ring

/-- C¹ on the compact interval implies every positive Hölder exponent ≤ 1. -/
lemma contDiffOn_holderOnInterval {β T : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {f : ℝ → 𝕜} (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) T)) :
    HolderOnInterval β T f := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hH : ∃ D, HolderOnWith D (NNReal.mk β hβ) f (Icc (0 : ℝ) T) :=
    HolderOnWith.exists_holderOnWith_of_le ⟨C,hC.holderOnWith⟩ (by exact hβ1) isCompact_Icc.isBounded
  exact (holderOnInterval_iff hβ f).mpr hH

/-- Continuous scalar data times the singular weight are absolutely integrable. -/
lemma weighted_integrable {α t : ℝ} (hα : 0 < α)
    {g : ℝ → 𝕜} (hg : ContinuousOn g (Icc (0 : ℝ) t)) :
    IntegrableOn (fun s => (t-s) ^ (α-1) • g s) (Ioc 0 t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact (reflected_power_integrable hα).smul_bdd C
    ((hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hC s ⟨hs.1.le,hs.2⟩)

lemma weighted_bound {α t C : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    {g : ℝ → 𝕜} (hg : ∀ s ∈ Icc (0 : ℝ) t, ‖g s‖ ≤ C) :
    ‖powerValue α g t‖ ≤ t ^ α / α * C := by
  rw [← reflected_power_integral hα ht, ← integral_mul_const]
  apply norm_integral_le_of_norm_le ((reflected_power_integrable hα).mul_const C)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
  exact mul_le_mul_of_nonneg_left (hg s ⟨hs.1.le,hs.2⟩)
    (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)

lemma holder_zero_bound {β T C : ℝ} {f : ℝ → 𝕜}
    (hf : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T,
      ‖f x-f y‖ ≤ C * |x-y| ^ β) (hf0 : f 0 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ‖f t‖ ≤ C * t ^ β := by
  simpa only [hf0, sub_zero, abs_of_nonneg ht.1] using hf t ht 0 ⟨le_rfl,ht.1.trans ht.2⟩

/-- Quantitative gain at zero. The two-time estimate is a separate obligation. -/
lemma fractional_endpoint_bound {α β T : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {f : ℝ → 𝕜} (hf : HolderOnInterval β T f) (hf0 : f 0 = 0) :
    ∃ C ≥ 0, ∀ t ∈ Icc (0 : ℝ) T,
      ‖fractionalValue α f t‖ ≤ C * t ^ (α+β) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨(Real.Gamma α)⁻¹ * (C/α), by positivity, fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · subst t
    simp [fractional_zero_time, Real.zero_rpow (by linarith : α+β ≠ 0)]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hb : ‖powerValue α f t‖ ≤ t ^ α / α * (C*t^β) := by
    apply weighted_bound hα ht.1
    intro s hs
    apply (holder_zero_bound hf hf0 ⟨hs.1,hs.2.trans ht.2⟩).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.1 hs.2 hβ.le) hC
  rw [fractionalValue, norm_smul, Real.norm_of_nonneg
    (inv_nonneg.mpr (Real.Gamma_pos_of_pos hα).le)]
  calc
    _ ≤ (Real.Gamma α)⁻¹ * (t ^ α / α * (C*t^β)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [Real.rpow_add htpos]; ring

lemma amplitude_zero_time (α : ℝ) (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) :
    amplitudeValue α k f 0 = 0 := by simp [amplitudeValue]

lemma remainder_zero_time (α : ℝ) (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) :
    remainderValue α k f 0 = 0 := by simp [remainderValue]

lemma smoothAmplitude_continuous_slice {T t : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) (ht : t ∈ Icc (0 : ℝ) T) :
    ContinuousOn (fun s => k (t,s)) (Icc (0 : ℝ) t) := by
  obtain ⟨U,hU,hTU,hk⟩ := hk
  exact hk.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun s hs => hTU ⟨hs.1,hs.2,ht.2⟩)

lemma smoothAmplitude_diagonal {T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) :
    ContDiffOn ℝ 1 (fun t => k (t,t)) (Icc (0 : ℝ) T) := by
  obtain ⟨U,hU,hTU,hk⟩ := hk
  exact hk.comp ((contDiff_id.prodMk contDiff_id).contDiffOn)
    (fun t ht => hTU ⟨ht.1,le_rfl,ht.2⟩)

/-- The decomposition is an identity between absolutely convergent integrals. -/
lemma amplitude_decomposition {α T : ℝ} (hα : 0 < α)
    {k : ℝ × ℝ → 𝕜} {f : ℝ → 𝕜} (hk : SmoothAmplitude T k)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntegrableOn (fun s => (t-s) ^ (α-1) • (k (t,s) * f s)) (Ioc 0 t) ∧
    IntegrableOn (fun s => (t-s) ^ (α-1) • ((k (t,s)-k (t,t)) * f s)) (Ioc 0 t) ∧
    amplitudeValue α k f t =
      k (t,t) * (Real.Gamma α • fractionalValue α f t) + remainderValue α k f t := by
  have hft : ContinuousOn f (Icc (0 : ℝ) t) :=
    hf.mono (Icc_subset_Icc_right ht.2)
  have hkt := smoothAmplitude_continuous_slice hk ht
  have hi := weighted_integrable hα (hkt.mul hft)
  change IntegrableOn (fun s => (t-s) ^ (α-1) • (k (t,s) * f s)) (Ioc 0 t) at hi
  have hir := weighted_integrable hα ((hkt.sub (continuousOn_const (c := k (t,t)))).mul hft)
  have hif := weighted_integrable hα hft
  refine ⟨hi,hir,?_⟩
  have hn : Real.Gamma α • fractionalValue α f t = powerValue α f t :=
    (normalization hα f t).symm
  rw [hn]
  have he : (fun s => (t-s) ^ (α-1) • ((k (t,s)-k (t,t)) * f s)) =
      (fun s => (t-s) ^ (α-1) • (k (t,s) * f s) -
        k (t,t) * ((t-s) ^ (α-1) • f s)) := by
    funext s
    rw [sub_mul, smul_sub, mul_smul_comm]
  rw [remainderValue, he, integral_sub hi (hif.const_mul (k (t,t))),
    integral_const_mul]
  change _ = k (t,t) * powerValue α f t +
    (amplitudeValue α k f t - k (t,t) * powerValue α f t)
  abel

lemma closedTriangle_eq (T : ℝ) :
    closedTriangle T = (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) ∩ {z | z.2 ≤ z.1} := by
  ext z
  simp only [closedTriangle, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_Icc]
  constructor
  · rintro ⟨h0,hs,ht⟩
    exact ⟨⟨⟨h0.trans hs,ht⟩,⟨h0,hs.trans ht⟩⟩,hs⟩
  · rintro ⟨⟨ht,hs⟩,hst⟩
    exact ⟨hs.1,hst,ht.2⟩

lemma isCompact_closedTriangle (T : ℝ) : IsCompact (closedTriangle T) := by
  rw [closedTriangle_eq]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_snd continuous_fst)

lemma convex_closedTriangle (T : ℝ) : Convex ℝ (closedTriangle T) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a*x.2+b*y.2 ∧ a*x.2+b*y.2 ≤ a*x.1+b*y.1 ∧ a*x.1+b*y.1 ≤ T
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
      (mul_le_mul_of_nonneg_left hy.2.1 hb), ?_⟩
  calc
    _ ≤ a*T+b*T := add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
      (mul_le_mul_of_nonneg_left hy.2.2 hb)
    _ = T := by rw [← add_mul,hab,one_mul]

/-- A uniform Lipschitz constant on the actual closed triangle, with no
rectangular or global C¹ hypothesis on the amplitude. -/
lemma smoothAmplitude_lipschitz {T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) : ∃ L, LipschitzOnWith L k (closedTriangle T) := by
  obtain ⟨U,hU,hTU,hk⟩ := hk
  exact (hk.mono hTU).exists_lipschitzOnWith (by norm_num)
    (convex_closedTriangle T) (isCompact_closedTriangle T)

/-- The extra order of vanishing in the remainder's bracket is uniform. -/
lemma smoothAmplitude_diagonal_bound {T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) :
    ∃ L ≥ 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) t,
      ‖k (t,s)-k (t,t)‖ ≤ L * (t-s) := by
  obtain ⟨L,hL⟩ := smoothAmplitude_lipschitz hk
  refine ⟨L,L.coe_nonneg,fun t ht s hs => ?_⟩
  have h := hL.dist_le_mul (t,s) ⟨hs.1,hs.2,ht.2⟩ (t,t) ⟨ht.1,le_rfl,ht.2⟩
  rw [dist_prod_same_left] at h
  simpa only [dist_eq_norm, Real.norm_eq_abs,
    abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr hs.2)] using h

/-- The remainder vanishes to order α+1 at zero. This estimate also gives the
zero endpoint derivative needed by a proof of continuous differentiability. -/
lemma remainder_endpoint_bound {α T : ℝ} (hα : 0 < α)
    {k : ℝ × ℝ → 𝕜} {f : ℝ → 𝕜} (hk : SmoothAmplitude T k)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    ∃ C ≥ 0, ∀ t ∈ Icc (0 : ℝ) T,
      ‖remainderValue α k f t‖ ≤ t ^ (α+1) / (α+1) * C := by
  obtain ⟨L,hL,hkL⟩ := smoothAmplitude_diagonal_bound hk
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨L*max M 0,by positivity,fun t ht => ?_⟩
  have hα1 : 0 < α+1 := by linarith
  have hmajor : IntegrableOn (fun s : ℝ => (t-s) ^ α * (L*max M 0)) (Ioc 0 t) := by
    simpa only [IntegrableOn, add_sub_cancel_right] using
      ((reflected_power_integrable (t := t) hα1).mul_const (L*max M 0))
  calc
    ‖remainderValue α k f t‖ ≤ ∫ s in Ioc 0 t, (t-s) ^ α * (L*max M 0) := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hr : 0 ≤ t-s := sub_nonneg.mpr hs.2
      rw [norm_smul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hr _)]
      calc
        _ ≤ (t-s) ^ (α-1) * (L*(t-s) * max M 0) := by
          gcongr
          · exact hkL t ht s ⟨hs.1.le,hs.2⟩
          · exact (hM s ⟨hs.1.le,hs.2.trans ht.2⟩).trans (le_max_left _ _)
        _ = ((t-s) ^ (α-1) * (t-s)) * (L*max M 0) := by ring
        _ = (t-s) ^ α * (L*max M 0) := by
          congr 1
          simpa only [sub_add_cancel] using
            (Real.rpow_add_one' hr (by linarith : α-1+1 ≠ 0)).symm
    _ = t ^ (α+1) / (α+1) * (L*max M 0) := by
      rw [integral_mul_const]
      congr 1
      simpa only [add_sub_cancel_right] using reflected_power_integral hα1 ht.1

/-- Packaging of the proved endpoint estimate. -/
theorem endpoint_bound : EndpointBound := by
  intro 𝕜 _ α β T hα hβ f hf hf0
  exact fractional_endpoint_bound hα hβ hf hf0

/-- Packaging of the proved integral identity and integrability assertions. -/
theorem amplitude_decomposition_on : AmplitudeDecomposition := by
  intro 𝕜 _ α T hα k f hk hf t ht
  exact amplitude_decomposition hα hk hf ht

/-- Assemble the remainder construction from its differentiability theorem. -/
theorem remainder_assembly : RemainderAssembly := by
  intro hR 𝕜 _ α T hα hα1 hT k f hk hf
  exact ⟨fun t ht => amplitude_decomposition hα hk hf ht,
    hR α T hα hα1 hT k f hk hf, remainder_zero_time α k f⟩

/-- Hölder algebra combines the fractional gain with the C¹ remainder. -/
theorem gain_assembly : GainAssembly := by
  intro hJ hR 𝕜 _ α β T hα hα1 hβ hβ1 hγ1 hT k f hk hf hf0
  have hγ : 0 < α+β := add_pos hα hβ
  have hfc := holderOnInterval_continuousOn hβ hf
  obtain ⟨hd,hRc,hR0⟩ := hR α T hα hα1 hT k f hk hfc
  obtain ⟨hJH,hJ0⟩ := hJ α β T hα hα1 hβ hβ1 hγ1 hT f hf hf0
  have hkH : HolderOnInterval (α+β) T (fun t => k (t,t)) :=
    contDiffOn_holderOnInterval hγ.le hγ1.le (smoothAmplitude_diagonal hk)
  have hRH : HolderOnInterval (α+β) T (remainderValue α k f) :=
    contDiffOn_holderOnInterval hγ.le hγ1.le hRc
  have hs := holderOnInterval_add
    (holderOnInterval_mul hγ hkH (holderOnInterval_const_smul hJH (Real.Gamma α))) hRH
  obtain ⟨C,hC,hs⟩ := hs
  refine ⟨⟨C,hC,fun x hx y hy => ?_⟩,amplitude_zero_time α k f⟩
  have h := hs x hx y hy
  change ‖(k (x,x) * (Real.Gamma α • fractionalValue α f x) + remainderValue α k f x) -
    (k (y,y) * (Real.Gamma α • fractionalValue α f y) + remainderValue α k f y)‖ ≤
    C * |x-y| ^ (α+β) at h
  rw [← (hd x hx).2.2, ← (hd y hy).2.2] at h
  exact h

/-- A quantitative mean-value estimate for the decreasing derivative of a power.
The lower endpoint is strictly positive; no differentiability at zero is used. -/
lemma rpow_sub_bound {p x y : ℝ} (hp : p ≤ 1) (hx : 0 < x) (hxy : x ≤ y) :
    ‖y ^ p - x ^ p‖ ≤ |p| * x ^ (p-1) * (y-x) := by
  have hd (z : ℝ) (hz : z ∈ Icc x y) :
      HasDerivAt (fun z : ℝ => z ^ p) (p * z ^ (p-1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hx.trans_le hz.1)))
  have hb (z : ℝ) (hz : z ∈ Icc x y) :
      ‖p * z ^ (p-1)‖ ≤ |p| * x ^ (p-1) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg
      (hx.le.trans hz.1) _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hz.1 (by linarith)) (abs_nonneg p)
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (fun z hz => (hd z hz).hasDerivWithinAt)
    (fun z hz => hb z (Ico_subset_Icc_self hz)) y ⟨hxy, le_rfl⟩

/-- The scalar cancellation kernel is integrable at both its singular endpoint
and infinity, precisely in the subcritical range α+β<1. -/
lemma increment_kernel_integrable {α β : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 ≤ β) (hγ : α+β < 1) :
    IntegrableOn (fun x : ℝ => ((x-1) ^ (α-1) - x ^ (α-1)) * x ^ β) (Ioi 1) := by
  let F : ℝ → ℝ := fun x => ((x-1) ^ (α-1) - x ^ (α-1)) * x ^ β
  have hc : ContinuousOn F (Ioi 1) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.sub
      · exact (continuousOn_id.sub continuousOn_const).rpow_const
          (fun x hx => Or.inl (by change x-1 ≠ 0; linarith [show 1 < x from hx]))
      · exact continuousOn_id.rpow_const
          (fun x hx => Or.inl (by change x ≠ 0; linarith [show 1 < x from hx]))
    · exact continuousOn_id.rpow_const
        (fun x hx => Or.inl (by change x ≠ 0; linarith [show 1 < x from hx]))
  have hnear : IntegrableOn F (Ioc 1 2) := by
    have hi : IntegrableOn (fun x : ℝ => (x-1) ^ (α-1)) (Ioc 1 2) := by
      have h := (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := 1) (by linarith : -1 < α-1)).comp_sub_right 1
      simpa only [zero_add, show (1:ℝ)+1=2 by norm_num] using h.1
    apply (hi.const_mul ((2 : ℝ)^β)).mono'
      ((hc.mono (fun x hx => hx.1)).aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : 0 < x-1 := by linarith [hx.1]
    have hx0 : 0 < x := by linarith [hx.1]
    have hdiff : 0 ≤ (x-1)^(α-1) - x^(α-1) := sub_nonneg.mpr
      (Real.rpow_le_rpow_of_nonpos hx1 (by linarith) (by linarith))
    rw [Real.norm_of_nonneg (mul_nonneg hdiff (Real.rpow_nonneg hx0.le _))]
    calc
      _ ≤ (x-1)^(α-1) * x^β :=
        mul_le_mul_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg hx0.le _))
          (Real.rpow_nonneg hx0.le _)
      _ ≤ (x-1)^(α-1) * (2:ℝ)^β :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le hx.2 hβ)
          (Real.rpow_nonneg hx1.le _)
      _ = _ := mul_comm _ _
  have hfar : IntegrableOn F (Ioi 2) := by
    have hi := integrableOn_Ioi_rpow_of_lt (a := α+β-2) (c := (2:ℝ))
      (by linarith) (by norm_num)
    apply (hi.const_mul ((1-α) * (2:ℝ)^(2-α))).mono'
      ((hc.mono (fun x hx => lt_trans (by norm_num) hx)).aestronglyMeasurable
        measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    have hx1 : 0 < x-1 := by linarith [show 2 < x from hx]
    have hmean := rpow_sub_bound (p := α-1) (by linarith) hx1 (by linarith : x-1 ≤ x)
    have hscale : (x-1)^(α-2) ≤ (2:ℝ)^(2-α) * x^(α-2) := by
      calc
        _ ≤ (x/2)^(α-2) := Real.rpow_le_rpow_of_nonpos
          (by positivity) (by linarith [show 2 < x from hx]) (by linarith)
        _ = _ := by
          rw [Real.div_rpow hx0.le (by norm_num)]
          rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ))]
          rw [show -(α-2) = 2-α by ring, mul_comm]
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hm : ‖(x-1)^(α-1) - x^(α-1)‖ ≤ (1-α) * (x-1)^(α-2) := by
      simpa only [norm_sub_rev, abs_of_nonpos (by linarith : α-1 ≤ 0),
        neg_sub, show α-1-1=α-2 by ring, show x-(x-1)=1 by ring, mul_one] using hmean
    calc
      _ ≤ ((1-α) * (x-1)^(α-2)) * x^β :=
        mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hx0.le _)
      _ ≤ ((1-α) * ((2:ℝ)^(2-α) * x^(α-2))) * x^β := by
        gcongr
      _ = ((1-α) * (2:ℝ)^(2-α)) * x^(α+β-2) := by
        rw [show α+β-2 = (α-2)+β by ring, Real.rpow_add hx0]; ring
  have he : Ioc (1:ℝ) 2 ∪ Ioi 2 = Ioi 1 := by
    ext x; simp only [mem_union, mem_Ioc, mem_Ioi]; constructor <;> grind
  rw [← he]
  exact hnear.union hfar

/-- Rescaling the cancellation integral produces a constant independent of the
two times. Its integrability contains the restriction α+β<1. -/
lemma increment_kernel_mass {α β : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 ≤ β) (hγ : α+β < 1) :
    ∃ K ≥ 0, ∀ h : ℝ, 0 < h →
      IntegrableOn (fun r : ℝ => ((r-h)^(α-1)-r^(α-1))*r^β) (Ioi h) ∧
      (∫ r in Ioi h, ((r-h)^(α-1)-r^(α-1))*r^β) = K*h^(α+β) := by
  let F : ℝ → ℝ := fun x => ((x-1)^(α-1)-x^(α-1))*x^β
  have hF : IntegrableOn F (Ioi 1) := increment_kernel_integrable hα hα1 hβ hγ
  have hFpos : 0 ≤ᵐ[volume.restrict (Ioi 1)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply mul_nonneg _ (Real.rpow_nonneg (by linarith [show 1 < x from hx]) _)
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos
      (by linarith [show 1 < x from hx]) (by linarith) (by linarith))
  refine ⟨∫ x in Ioi 1, F x, integral_nonneg_of_ae hFpos, fun h hh => ?_⟩
  let G : ℝ → ℝ := fun r => ((r-h)^(α-1)-r^(α-1))*r^β
  have he : (fun x => G (h*x)) =ᵐ[volume.restrict (Ioi 1)]
      (fun x => h^(α+β-1) * F x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := by linarith [show 1 < x from hx]
    have hx1 : 0 ≤ x-1 := by linarith [show 1 < x from hx]
    dsimp [G,F]
    rw [show h*x-h = h*(x-1) by ring, Real.mul_rpow hh.le hx1,
      Real.mul_rpow hh.le hx0, Real.mul_rpow hh.le hx0,
      show α+β-1 = (α-1)+β by ring, Real.rpow_add hh]
    ring
  have hi : IntegrableOn G (Ioi h) := by
    have hc := (hF.const_mul (h^(α+β-1))).congr he.symm
    simpa only [mul_one] using
      (integrableOn_Ioi_comp_mul_left_iff G 1 hh).mp hc
  refine ⟨hi, ?_⟩
  calc
    (∫ r in Ioi h, G r) = h * ∫ x in Ioi 1, G (h*x) := by
      simpa only [mul_one, smul_eq_mul] using
        (integral_comp_mul_left_Ioi' G 1 hh).symm
    _ = h * (h^(α+β-1) * ∫ x in Ioi 1, F x) := by
      rw [integral_congr_ae he, integral_const_mul]
    _ = (∫ x in Ioi 1, F x) * h^(α+β) := by
      calc
        _ = (∫ x in Ioi 1, F x) * (h^(α+β-1)*h) := by ring
        _ = _ := by rw [← Real.rpow_add_one hh.ne', sub_add_cancel]

/-- The constant removed from a centered increment satisfies the same gain.
The zero boundary condition supplies the factor t^β in its application. -/
lemma constant_increment_bound {α β : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 ≤ β) (hγ : α+β < 1) :
    ∃ D ≥ 0, ∀ u t : ℝ, 0 ≤ u → u < t →
      ‖(t^α-u^α)/α‖ * t^β ≤ D * (t-u)^(α+β) := by
  refine ⟨(2:ℝ)^(α+β)/α + (2:ℝ)^(1-α), by positivity, fun u t hu hut => ?_⟩
  have ht : 0 < t := hu.trans_lt hut
  have hh : 0 < t-u := sub_pos.mpr hut
  have hd : 0 ≤ t^α-u^α := sub_nonneg.mpr (Real.rpow_le_rpow hu hut.le hα.le)
  rw [Real.norm_of_nonneg (div_nonneg hd hα.le)]
  by_cases hsmall : t ≤ 2*(t-u)
  · calc
      _ ≤ (t^α/α)*t^β := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg hu _)) hα.le)
        (Real.rpow_nonneg ht.le _)
      _ = t^(α+β)/α := by rw [Real.rpow_add ht]; ring
      _ ≤ ((2*(t-u))^(α+β))/α := by gcongr <;> linarith
      _ = ((2:ℝ)^(α+β)/α)*(t-u)^(α+β) := by
        rw [Real.mul_rpow (by norm_num) hh.le]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg hh.le _)
  · have hu0 : 0 < u := by linarith
    have hm := rpow_sub_bound hα1.le hu0 hut.le
    rw [Real.norm_of_nonneg hd, abs_of_pos hα] at hm
    have hm' : (t^α-u^α)/α ≤ u^(α-1)*(t-u) :=
      (div_le_iff₀ hα).mpr (by nlinarith [hm])
    have hs : u^(α-1) ≤ (2:ℝ)^(1-α)*t^(α-1) := by
      calc
        _ ≤ (t/2)^(α-1) := Real.rpow_le_rpow_of_nonpos (by positivity)
          (by linarith) (by linarith)
        _ = _ := by
          rw [Real.div_rpow ht.le (by norm_num), div_eq_mul_inv,
            ← Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ)),
            show -(α-1) = 1-α by ring, mul_comm]
    calc
      _ ≤ (u^(α-1)*(t-u))*t^β := mul_le_mul_of_nonneg_right hm' (by positivity)
      _ ≤ (((2:ℝ)^(1-α)*t^(α-1))*(t-u))*t^β := by gcongr
      _ = (2:ℝ)^(1-α)*(t-u)*t^(α+β-1) := by
        rw [show α+β-1 = (α-1)+β by ring, Real.rpow_add ht]; ring
      _ ≤ (2:ℝ)^(1-α)*(t-u)*(t-u)^(α+β-1) := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hh (by linarith) (by linarith))
          (by positivity)
      _ = (2:ℝ)^(1-α)*(t-u)^(α+β) := by
        rw [mul_assoc, mul_comm (t-u), ← Real.rpow_add_one hh.ne']
        congr 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by positivity)) (Real.rpow_nonneg hh.le _)

/-- Continuity of weak triangular integrals with continuous amplitudes. -/
lemma continuousOn_amplitudeValue {α T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    {k : ℝ × ℝ → 𝕜} {f : ℝ → 𝕜}
    (hk : ContinuousOn k (closedTriangle T))
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    ContinuousOn (amplitudeValue α k f) (Icc (0 : ℝ) T) := by
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · subst T
    simpa only [Icc_self] using continuousOn_singleton (amplitudeValue α k f) 0
  let I := Icc (0 : ℝ) T
  have hkc : Continuous (fun p : I × I => k ((p.1 : ℝ), min (p.2 : ℝ) (p.1 : ℝ))) := by
    apply hk.comp_continuous
    · exact (continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd).min
          (continuous_subtype_val.comp continuous_fst))
    · intro p
      exact ⟨le_min p.2.property.1 p.1.property.1, min_le_right _ _, p.1.property.2⟩
  have hfc : Continuous (fun p : I × I => f (p.2 : ℝ)) :=
    hf.comp_continuous (continuous_subtype_val.comp continuous_snd) (fun p => p.2.property)
  let G : C(I × I, 𝕜) := ⟨_, hkc.mul hfc⟩
  obtain ⟨J,hJ,hJn⟩ := continuous_construction (𝕜 := 𝕜) α T hα hTpos
  have hcont : Continuous (fun t : I => Real.Gamma α • (J (G.curry t)) t) :=
    continuous_const.smul ((J.continuous.comp G.curry.continuous).eval continuous_id)
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hcont.congr
  intro t
  rw [(hJ (G.curry t) t).2]
  have hn : Real.Gamma α • fractionalValue α (continuousExtension hTpos.le (G.curry t)) t =
      powerValue α (continuousExtension hTpos.le (G.curry t)) t :=
    (normalization hα (continuousExtension hTpos.le (G.curry t)) t).symm
  rw [hn]
  change powerValue α (continuousExtension hTpos.le (G.curry t)) t = amplitudeValue α k f t
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le,hs.2.trans t.property.2⟩
  simp only [continuousExtension, projIcc_of_mem hTpos.le hsT, ContinuousMap.curry_apply]
  change (t.val - s) ^ (α-1) • (k (t.val, min s t.val) * f s) = _
  rw [min_eq_left hs.2]

/-- Measurability of the compact integration triangle. -/
lemma measurableSet_closedTriangle (T : ℝ) : MeasurableSet (closedTriangle T) := by
  exact (isCompact_closedTriangle T).isClosed.measurableSet

lemma triangle_slice_left {E : Type*} [Zero E] {T x : ℝ} (hx : x ∈ Icc (0:ℝ) T)
    (F : ℝ × ℝ → E) :
    (fun s => (closedTriangle T).indicator F (x,s)) =
      (Icc (0:ℝ) x).indicator (fun s => F (x,s)) := by
  funext s
  have he : (x,s) ∈ closedTriangle T ↔ s ∈ Icc (0:ℝ) x := by
    change (0 ≤ s ∧ s ≤ x ∧ x ≤ T) ↔ (0 ≤ s ∧ s ≤ x)
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hx.2⟩⟩
  simp only [indicator, he]

lemma triangle_slice_right {E : Type*} [Zero E] {T s : ℝ} (hs : 0 ≤ s)
    (F : ℝ × ℝ → E) :
    (fun x => (closedTriangle T).indicator F (x,s)) =
      (Icc s T).indicator (fun x => F (x,s)) := by
  funext x
  have he : (x,s) ∈ closedTriangle T ↔ x ∈ Icc s T := by
    change (0 ≤ s ∧ s ≤ x ∧ x ≤ T) ↔ (s ≤ x ∧ x ≤ T)
    tauto
  simp only [indicator, he]

lemma triangle_left_inter {T x : ℝ} (hx : x ≤ T) :
    Icc (0:ℝ) x ∩ Ioc 0 T = Ioc 0 x := by
  ext s; simp only [mem_inter_iff, mem_Icc, mem_Ioc]
  constructor
  · intro h; exact ⟨h.2.1,h.1.2⟩
  · intro h; exact ⟨⟨h.1.le,h.2⟩,h.1,h.2.trans hx⟩

lemma triangle_right_inter {T s : ℝ} (hs : 0 < s) :
    Icc s T ∩ Ioc (0:ℝ) T = Icc s T := by
  ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioc]
  constructor
  · tauto
  · intro h; exact ⟨h,lt_of_lt_of_le hs h.1,h.2⟩

lemma triangle_left_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T x : ℝ} (hx : x ∈ Icc (0:ℝ) T) (F : ℝ × ℝ → E) :
    (∫ s in Ioc 0 T, (closedTriangle T).indicator F (x,s)) =
      ∫ s in Ioc 0 x, F (x,s) := by
  rw [triangle_slice_left hx F, integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, triangle_left_inter hx.2]

lemma triangle_right_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T s : ℝ} (hs : 0 < s) (F : ℝ × ℝ → E) :
    (∫ x in Ioc 0 T, (closedTriangle T).indicator F (x,s)) =
      ∫ x in Ioc s T, F (x,s) := by
  rw [triangle_slice_right hs.le F, integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, triangle_right_inter hs,
    integral_Icc_eq_integral_Ioc]

lemma triangle_weight_integrable {α T : ℝ} (hα : 0 < α) :
    Integrable ((closedTriangle T).indicator (fun z : ℝ × ℝ => (z.1-z.2)^(α-1)))
      ((volume.restrict (Ioc (0:ℝ) T)).prod (volume.restrict (Ioc (0:ℝ) T))) := by
  let W : ℝ × ℝ → ℝ :=
    (closedTriangle T).indicator (fun z : ℝ × ℝ => (z.1-z.2)^(α-1))
  have hW : AEStronglyMeasurable W
      ((volume.restrict (Ioc (0:ℝ) T)).prod (volume.restrict (Ioc (0:ℝ) T))) := by
    apply AEStronglyMeasurable.indicator _ (measurableSet_closedTriangle T)
    exact ((measurable_fst.sub measurable_snd).pow_const (α-1)).aestronglyMeasurable
  apply (integrable_prod_iff hW).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change Integrable (fun s => (closedTriangle T).indicator _ (x,s)) _
    rw [triangle_slice_left ⟨hx.1.le,hx.2⟩ _, integrable_indicator_iff measurableSet_Icc]
    change Integrable _ ((volume.restrict _).restrict _)
    rw [Measure.restrict_restrict measurableSet_Icc, triangle_left_inter hx.2]
    exact reflected_power_integrable hα
  · have hb : IntegrableOn (fun x : ℝ => x^α/α) (Ioc 0 T) := by
      have hc : ContinuousOn (fun x : ℝ => x^α/α) (Icc (0:ℝ) T) :=
        (continuousOn_id.rpow_const (fun x _ => Or.inr hα.le)).div_const α
      exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    apply hb.mono' hW.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have he : (fun s => ‖W (x,s)‖) =
        fun s => (closedTriangle T).indicator (fun z : ℝ × ℝ => ‖(z.1-z.2)^(α-1)‖) (x,s) := by
      funext s
      simp only [W, norm_indicator_eq_indicator_norm]
    rw [he,triangle_left_integral ⟨hx.1.le,hx.2⟩]
    have hn : (∫ s in Ioc 0 x, ‖(x-s)^(α-1)‖) = x^α/α := by
      rw [← reflected_power_integral hα hx.1.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
    rw [hn,Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg hx.1.le _) hα.le)]

lemma weighted_triangle_product_integrable {α T : ℝ} (hα : 0 < α)
    {A : ℝ × ℝ → 𝕜} (hA : ContinuousOn A (closedTriangle T)) :
    Integrable ((closedTriangle T).indicator (fun z : ℝ × ℝ =>
      (z.1-z.2)^(α-1) • A z))
      ((volume.restrict (Ioc (0:ℝ) T)).prod (volume.restrict (Ioc (0:ℝ) T))) := by
  let μ := (volume.restrict (Ioc (0:ℝ) T)).prod (volume.restrict (Ioc (0:ℝ) T))
  let W := (closedTriangle T).indicator (fun z : ℝ × ℝ => (z.1-z.2)^(α-1) • A z)
  have hm : AEStronglyMeasurable W μ := by
    apply (aestronglyMeasurable_indicator_iff (measurableSet_closedTriangle T)).mpr
    exact (((measurable_fst.sub measurable_snd).pow_const (α-1)).aestronglyMeasurable.restrict).smul
      (hA.aestronglyMeasurable (measurableSet_closedTriangle T))
  obtain ⟨C,hC⟩ := (isCompact_closedTriangle T).exists_bound_of_continuousOn hA
  apply ((triangle_weight_integrable hα).const_mul (max C 0)).mono' hm
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ closedTriangle T
  · simp only [W,indicator_of_mem hz,norm_smul]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [hz.2.1] : 0 ≤ z.1-z.2) _)]
    calc
      _ ≤ (z.1-z.2)^(α-1) * max C 0 :=
        mul_le_mul_of_nonneg_left ((hC z hz).trans (le_max_left _ _))
          (Real.rpow_nonneg (by linarith [hz.2.1]) _)
      _ = _ := mul_comm _ _
  · simp only [W,indicator_of_notMem hz,norm_zero,mul_zero,le_refl]

lemma weighted_triangle_fubini {α T : ℝ} (hα : 0 < α)
    {A : ℝ × ℝ → 𝕜} (hA : ContinuousOn A (closedTriangle T)) :
    (∫ s in Ioc 0 T, ∫ x in Ioc s T, (x-s)^(α-1) • A (x,s)) =
      ∫ x in Ioc 0 T, ∫ s in Ioc 0 x, (x-s)^(α-1) • A (x,s) := by
  let F : ℝ × ℝ → 𝕜 := fun z => (z.1-z.2)^(α-1) • A z
  let W := (closedTriangle T).indicator F
  have hi := weighted_triangle_product_integrable hα hA
  have he := integral_integral_swap (f := fun x s => W (x,s)) hi
  calc
    _ = ∫ s in Ioc 0 T, ∫ x in Ioc 0 T, W (x,s) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (triangle_right_integral hs.1 F).symm
    _ = ∫ x in Ioc 0 T, ∫ s in Ioc 0 T, W (x,s) := he.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact triangle_left_integral ⟨hx.1.le,hx.2⟩ F

lemma contDiffOn_of_eq_integral {T : ℝ} (hT : 0 ≤ T)
    {R D : ℝ → 𝕜} (hD : ContinuousOn D (Icc (0 : ℝ) T))
    (hR : ∀ t ∈ Icc (0 : ℝ) T, R t = ∫ s in Ioc 0 t, D s) :
    ContDiffOn ℝ 1 R (Icc (0 : ℝ) T) := by
  let De : ℝ → 𝕜 := fun s => D (projIcc 0 T hT s)
  have hDe : Continuous De :=
    hD.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc 0 T hT s).property)
  let P : ℝ → 𝕜 := fun t => ∫ s in (0 : ℝ)..t, De s
  have hPder (t : ℝ) : HasDerivAt P (De t) t :=
    intervalIntegral.integral_hasDerivAt_right (hDe.intervalIntegrable 0 t)
      hDe.stronglyMeasurable.stronglyMeasurableAtFilter hDe.continuousAt
  have hPc : ContDiff ℝ 1 P := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t => (hPder t).differentiableAt, ?_⟩
    exact hDe.congr (fun t => (hPder t).deriv.symm)
  apply hPc.contDiffOn.congr
  intro t ht
  rw [hR t ht]
  change (∫ s in Ioc 0 t, D s) = ∫ s in (0 : ℝ)..t, De s
  rw [intervalIntegral.integral_of_le ht.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le,hs.2.trans ht.2⟩
  dsimp [De]
  rw [projIcc_of_mem hT hsT]

lemma powerValue_centered {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    {f : ℝ → 𝕜} (hf : ContinuousOn f (Icc (0:ℝ) t)) (c : 𝕜) :
    powerValue α f t = powerValue α (fun s => f s-c) t + (t^α/α) • c := by
  have hi := weighted_integrable hα hf
  have hic := (reflected_power_integrable (t := t) hα).smul_const c
  have he : (fun s => (t-s)^(α-1) • (f s-c)) =
      (fun s => (t-s)^(α-1) • f s - (t-s)^(α-1) • c) := by
    ext s; exact smul_sub _ _ _
  simp only [powerValue]
  rw [he, integral_sub hi hic, integral_smul_const,
    reflected_power_integral hα ht]
  change _ = (_ - _) + _
  abel

lemma shifted_powerValue {α u t : ℝ} (hu : 0 ≤ u) (g : ℝ → 𝕜) :
    powerValue α g u = ∫ r in t-u..t, (r-(t-u))^(α-1) • g (t-r) := by
  rw [powerValue, ← intervalIntegral.integral_of_le hu]
  have he := intervalIntegral.integral_comp_sub_left
    (fun r => (r-(t-u))^(α-1) • g (t-r)) (a := (0:ℝ)) (b := u) t
  simpa only [sub_sub_sub_cancel_left, sub_sub_cancel, sub_zero] using he

lemma shifted_weighted_integrable {α u t : ℝ} (hα : 0 < α) (hu : 0 ≤ u)
    {g : ℝ → 𝕜} (hg : ContinuousOn g (Icc (0:ℝ) u)) :
    IntervalIntegrable (fun r => (r-(t-u))^(α-1) • g (t-r)) volume (t-u) t := by
  have hi : IntervalIntegrable (fun s => (u-s)^(α-1) • g s) volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).mpr (weighted_integrable hα hg)
  have he := (hi.comp_sub_left t).symm
  simpa only [show ∀ x : ℝ, u-(t-x)=x-(t-u) by intro x; ring, sub_zero] using he

lemma short_centered_bound {α β T C u t : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hut : u < t) (htT : t ≤ T)
    {f : ℝ → 𝕜}
    (hf : ∀ x ∈ Icc (0:ℝ) T, ∀ y ∈ Icc (0:ℝ) T,
      ‖f x-f y‖ ≤ C * |x-y|^β) :
    ‖∫ r in (0:ℝ)..(t-u), r^(α-1) • (f (t-r)-f t)‖ ≤
      C * (t-u)^(α+β)/(α+β) := by
  have hh : 0 < t-u := sub_pos.mpr hut
  have hγ : 0 < α+β := add_pos hα hβ
  have hi := (power_integrable (T := t-u) hγ).const_mul C
  rw [intervalIntegral.integral_of_le hh.le]
  calc
    _ ≤ ∫ r in Ioc 0 (t-u), C*r^(α+β-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hr0 : 0 < r := hr.1
      have htr : t-r ∈ Icc (0:ℝ) T := ⟨by linarith [hr.2], by linarith⟩
      have ht : t ∈ Icc (0:ℝ) T := ⟨hu.trans hut.le,htT⟩
      have hdiff : ‖f (t-r)-f t‖ ≤ C*r^β := by
        simpa only [show t-r-t = -r by ring, abs_neg, abs_of_pos hr0] using hf (t-r) htr t ht
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr0.le _)]
      calc
        _ ≤ r^(α-1) * (C*r^β) := mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = _ := by rw [show α+β-1 = (α-1)+β by ring, Real.rpow_add hr0]; ring
    _ = C * (t-u)^(α+β)/(α+β) := by rw [integral_const_mul, power_integral hγ hh.le]; ring

lemma long_centered_bound {α β T C u t K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hC : 0 ≤ C) (hu : 0 ≤ u) (hut : u < t) (htT : t ≤ T)
    {f : ℝ → 𝕜}
    (hf : ∀ x ∈ Icc (0:ℝ) T, ∀ y ∈ Icc (0:ℝ) T,
      ‖f x-f y‖ ≤ C * |x-y|^β)
    (hi : IntegrableOn (fun r : ℝ => ((r-(t-u))^(α-1)-r^(α-1))*r^β) (Ioi (t-u)))
    (hm : (∫ r in Ioi (t-u), ((r-(t-u))^(α-1)-r^(α-1))*r^β) = K*(t-u)^(α+β)) :
    ‖∫ r in (t-u)..t, (r^(α-1)-(r-(t-u))^(α-1)) • (f (t-r)-f t)‖ ≤
      C*K*(t-u)^(α+β) := by
  let G : ℝ → ℝ := fun r => ((r-(t-u))^(α-1)-r^(α-1))*r^β
  have hht : t-u ≤ t := by linarith
  have hpos (r : ℝ) (hr : r ∈ Ioi (t-u)) : 0 ≤ G r := by
    apply mul_nonneg _ (Real.rpow_nonneg (by linarith [show t-u<r from hr]) _)
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos
      (by linarith [show t-u<r from hr]) (by linarith) (by linarith))
  have hb : (∫ r in Ioc (t-u) t, G r) ≤ K*(t-u)^(α+β) := by
    rw [← hm]
    exact setIntegral_mono_set hi
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr; exact hpos r hr)
      (Filter.Eventually.of_forall (fun r hr => hr.1))
  rw [intervalIntegral.integral_of_le hht]
  calc
    _ ≤ ∫ r in Ioc (t-u) t, C*G r := by
      apply norm_integral_le_of_norm_le ((hi.mono_set Ioc_subset_Ioi_self).const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hr0 : 0 < r := by linarith [hr.1]
      have htr : t-r ∈ Icc (0:ℝ) T := ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have ht : t ∈ Icc (0:ℝ) T := ⟨hu.trans hut.le,htT⟩
      have hdiff : ‖f (t-r)-f t‖ ≤ C*r^β := by
        simpa only [show t-r-t = -r by ring, abs_neg, abs_of_pos hr0] using hf (t-r) htr t ht
      have hd : r^(α-1) - (r-(t-u))^(α-1) ≤ 0 := sub_nonpos.mpr
        (Real.rpow_le_rpow_of_nonpos (by linarith [hr.1]) (by linarith) (by linarith))
      rw [norm_smul, Real.norm_of_nonpos hd]
      calc
        _ ≤ -(r^(α-1)-(r-(t-u))^(α-1)) * (C*r^β) :=
          mul_le_mul_of_nonneg_left hdiff (by linarith)
        _ = _ := by ring
    _ = C * ∫ r in Ioc (t-u) t, G r := integral_const_mul _ _
    _ ≤ C * (K*(t-u)^(α+β)) := mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

lemma powerValue_increment_bound {α β T C K D : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hβ : 0 < β) (hC : 0 ≤ C) {f : ℝ → 𝕜}
    (hf : ∀ x ∈ Icc (0:ℝ) T, ∀ y ∈ Icc (0:ℝ) T,
      ‖f x-f y‖ ≤ C * |x-y|^β) (hf0 : f 0=0)
    (hK : ∀ h : ℝ, 0 < h →
      IntegrableOn (fun r : ℝ => ((r-h)^(α-1)-r^(α-1))*r^β) (Ioi h) ∧
      (∫ r in Ioi h, ((r-h)^(α-1)-r^(α-1))*r^β) = K*h^(α+β))
    (hD : ∀ u t : ℝ, 0 ≤ u → u < t →
      ‖(t^α-u^α)/α‖ * t^β ≤ D * (t-u)^(α+β))
    {u t : ℝ} (hu : u ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (hut : u < t) :
    ‖powerValue α f t-powerValue α f u‖ ≤
      C*(1/(α+β)+K+D)*(t-u)^(α+β) := by
  have hh : 0 < t-u := sub_pos.mpr hut
  have hht : t-u ≤ t := by linarith [hu.1]
  have hfc : ContinuousOn f (Icc (0:ℝ) T) :=
    holderOnInterval_continuousOn hβ ⟨C,hC,hf⟩
  let g : ℝ → 𝕜 := fun s => f s-f t
  have hgt : ContinuousOn g (Icc (0:ℝ) t) :=
    (hfc.mono (Icc_subset_Icc_right ht.2)).sub continuousOn_const
  have hgu : ContinuousOn g (Icc (0:ℝ) u) :=
    hgt.mono (Icc_subset_Icc_right hut.le)
  have hpcT : powerValue α f t = powerValue α g t + (t^α/α) • f t :=
    powerValue_centered hα ht.1 (hfc.mono (Icc_subset_Icc_right ht.2)) (f t)
  have hpcU : powerValue α f u = powerValue α g u + (u^α/α) • f t :=
    powerValue_centered hα hu.1 (hfc.mono (Icc_subset_Icc_right hu.2)) (f t)
  have hpt : powerValue α g t = ∫ r in (0:ℝ)..t, r^(α-1) • g (t-r) := by
    rw [powerValue_reflect α g ht.1, intervalIntegral.integral_of_le ht.1]
  have hpu := shifted_powerValue (t := t) (α := α) hu.1 g
  have hA : IntervalIntegrable (fun r => r^(α-1) • g (t-r)) volume 0 t := by
    simpa only [sub_self, sub_zero] using
      (shifted_weighted_integrable (t := t) hα ht.1 hgt)
  have hA0h := hA.mono_set (by
    rw [uIcc_of_le hh.le, uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl hht)
  have hAht := hA.mono_set (by
    rw [uIcc_of_le hht, uIcc_of_le ht.1]
    exact Icc_subset_Icc hh.le le_rfl)
  have hB := shifted_weighted_integrable (t := t) hα hu.1 hgu
  have hlong : (∫ r in (t-u)..t,
      (r^(α-1)-(r-(t-u))^(α-1)) • g (t-r)) =
      (∫ r in (t-u)..t, r^(α-1) • g (t-r)) -
      (∫ r in (t-u)..t, (r-(t-u))^(α-1) • g (t-r)) := by
    simp_rw [sub_smul]
    exact intervalIntegral.integral_sub hAht hB
  have he : powerValue α f t-powerValue α f u =
      ((∫ r in (0:ℝ)..(t-u), r^(α-1) • g (t-r)) +
      (∫ r in (t-u)..t, (r^(α-1)-(r-(t-u))^(α-1)) • g (t-r))) +
      ((t^α-u^α)/α) • f t := by
    rw [hpcT,hpcU,hpt,hpu,hlong,
      ← intervalIntegral.integral_add_adjacent_intervals hA0h hAht,
      sub_div, sub_smul]
    abel
  have hshort := short_centered_bound hα hβ hC hu.1 hut ht.2 hf
  have hlongB := long_centered_bound hα hα1 hβ hC hu.1 hut ht.2 hf (hK (t-u) hh).1 (hK (t-u) hh).2
  have hconstant : ‖((t^α-u^α)/α) • f t‖ ≤ C*D*(t-u)^(α+β) := by
    rw [norm_smul]
    calc
      _ ≤ ‖(t^α-u^α)/α‖ * (C*t^β) := mul_le_mul_of_nonneg_left (holder_zero_bound hf hf0 ht) (norm_nonneg _)
      _ = C * (‖(t^α-u^α)/α‖ * t^β) := by ring
      _ ≤ C * (D*(t-u)^(α+β)) := mul_le_mul_of_nonneg_left (hD u t hu.1 hut) hC
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ (‖∫ r in (0:ℝ)..(t-u), r^(α-1) • g (t-r)‖ +
      ‖∫ r in (t-u)..t, (r^(α-1)-(r-(t-u))^(α-1)) • g (t-r)‖) +
      ‖((t^α-u^α)/α) • f t‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (C*(t-u)^(α+β)/(α+β)+C*K*(t-u)^(α+β)) + C*D*(t-u)^(α+β) :=
      add_le_add (add_le_add hshort hlongB) hconstant
    _ = _ := by ring

/-- The full two-time gain on the closed interval, including the zero boundary. -/
theorem fractional_gain : FractionalGain := by
  intro 𝕜 _ α β T hα hα1 hβ hβ1 hγ1 hT f hf hf0
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨K,hK0,hK⟩ := increment_kernel_mass hα hα1 hβ.le hγ1
  obtain ⟨D,hD0,hD⟩ := constant_increment_bound hα hα1 hβ.le hγ1
  have hγ : 0 < α+β := add_pos hα hβ
  have hpower : HolderOnInterval (α+β) T (powerValue α f) := by
    refine ⟨C*(1/(α+β)+K+D), by positivity, fun x hx y hy => ?_⟩
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · rw [norm_sub_rev]
      simpa only [abs_of_nonpos (sub_nonpos.mpr hxy.le), neg_sub] using
        (powerValue_increment_bound hα hα1 hβ hC hf hf0 hK hD hx hy hxy)
    · subst y
      simp [Real.zero_rpow hγ.ne']
    · simpa only [abs_of_pos (sub_pos.mpr hyx)] using
        (powerValue_increment_bound hα hα1 hβ hC hf hf0 hK hD hy hx hyx)
  refine ⟨?_,fractional_zero_time α f⟩
  exact holderOnInterval_const_smul hpower (Real.Gamma α)⁻¹

def amplitudeSlope (k : ℝ × ℝ → 𝕜) (z : ℝ × ℝ) : 𝕜 :=
  -(∫ θ in Ioc (0 : ℝ) 1,
    fderiv ℝ k (z.1, z.1 + θ * (z.2-z.1)) (0,1))

lemma segment_in_triangle {T : ℝ} {z : ℝ × ℝ} (hz : z ∈ closedTriangle T)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (z.1, z.1 + θ * (z.2-z.1)) ∈ closedTriangle T := by
  rcases hz with ⟨hs, hst, ht⟩
  constructor
  · nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hst),
      mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hst)]
  constructor
  · nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hst)]
  · exact ht

lemma smoothAmplitude_continuous_fderiv {T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) : ContinuousOn (fderiv ℝ k) (closedTriangle T) := by
  obtain ⟨U, hU, hTU, hkU⟩ := hk
  exact (hkU.continuousOn_fderiv_of_isOpen hU le_rfl).mono hTU

lemma smoothAmplitude_hasFDerivAt {T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) {z : ℝ × ℝ} (hz : z ∈ closedTriangle T) :
    HasFDerivAt k (fderiv ℝ k z) z := by
  obtain ⟨U, hU, hTU, hkU⟩ := hk
  exact ((hkU.differentiableOn (by decide)).differentiableAt
    (hU.mem_nhds (hTU hz))).hasFDerivAt

lemma amplitudeSlope_continuousOn {T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) : ContinuousOn (amplitudeSlope k) (closedTriangle T) := by
  let g : (ℝ × ℝ) → ℝ → 𝕜 := fun z θ =>
    fderiv ℝ k (z.1, z.1 + θ * (z.2-z.1)) (0,1)
  have hfd := smoothAmplitude_continuous_fderiv hk
  have hgc : ∀ z ∈ closedTriangle T, ContinuousOn (g z) (Icc (0 : ℝ) 1) := by
    intro z hz
    exact (hfd.comp (by fun_prop) (fun θ hθ => segment_in_triangle hz hθ)).clm_apply
      continuousOn_const
  obtain ⟨M, hM⟩ := (isCompact_closedTriangle T).exists_bound_of_continuousOn
    (hfd.clm_apply (continuousOn_const (c := ((0,1) : ℝ × ℝ))))
  rw [continuousOn_iff_continuous_domRestrict]
  apply Continuous.neg
  apply continuous_iff_continuousAt.mpr
  intro z₀
  apply continuousAt_of_dominated
  · filter_upwards with z
    exact ((hgc z z.property).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards with z
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hM _ (segment_in_triangle z.property ⟨hθ.1.le,hθ.2⟩)
  · exact integrableOn_const (by simp)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    apply ContinuousAt.clm_apply _ continuousAt_const
    exact ((hfd.comp_continuous (by fun_prop)
      (fun z => segment_in_triangle z.property ⟨hθ.1.le,hθ.2⟩))).continuousAt

lemma amplitudeSlope_identity {T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) {z : ℝ × ℝ} (hz : z ∈ closedTriangle T) :
    k z - k (z.1,z.1) = (z.1-z.2) • amplitudeSlope k z := by
  let g : ℝ → 𝕜 := fun θ => k (z.1, z.1 + θ * (z.2-z.1))
  let g' : ℝ → 𝕜 := fun θ => fderiv ℝ k (z.1,z.1+θ*(z.2-z.1)) (0,1)
  have hg : ∀ θ ∈ Icc (0 : ℝ) 1, HasDerivAt g ((z.2-z.1) • g' θ) θ := by
    intro θ hθ
    have hi : HasDerivAt (fun θ : ℝ => (z.1, z.1+θ*(z.2-z.1)))
        (0,z.2-z.1) θ := by
      convert (hasDerivAt_const θ z.1).prodMk
        (((hasDerivAt_id θ).mul_const (z.2-z.1)).const_add z.1) using 1 <;> simp
    have h := (smoothAmplitude_hasFDerivAt hk (segment_in_triangle hz hθ)).comp_hasDerivAt θ hi
    have hv : ((0,z.2-z.1) : ℝ × ℝ) = (z.2-z.1) • ((0,1) : ℝ × ℝ) := by
      ext <;> simp
    simpa only [g, Function.comp_def, hv, map_smul] using h
  have hc : ContinuousOn g' (Icc (0 : ℝ) 1) :=
    ((smoothAmplitude_continuous_fderiv hk).comp (by fun_prop)
      (fun θ hθ => segment_in_triangle hz hθ)).clm_apply continuousOn_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun θ hθ => hg θ (by simpa using hθ))
    ((hc.const_smul (z.2-z.1)).intervalIntegrable_of_Icc zero_le_one)
  rw [intervalIntegral.integral_smul] at he
  rw [show z.2-z.1 = -(z.1-z.2) by ring, neg_smul] at he
  simpa [g, g', amplitudeSlope, intervalIntegral.integral_of_le zero_le_one, smul_neg]
    using he.symm

def remainderDerivativeAmplitude (α : ℝ) (k : ℝ × ℝ → 𝕜) (z : ℝ × ℝ) : 𝕜 :=
  (α-1) • amplitudeSlope k z + fderiv ℝ k z (1,0) -
    fderiv ℝ k (z.1,z.1) (1,1)

lemma remainderDerivativeAmplitude_continuousOn {α T : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) :
    ContinuousOn (remainderDerivativeAmplitude α k) (closedTriangle T) := by
  have hfd := smoothAmplitude_continuous_fderiv hk
  apply ContinuousOn.sub
  · exact ((amplitudeSlope_continuousOn hk).const_smul (α-1)).add
      (hfd.clm_apply continuousOn_const)
  · apply (hfd.comp (by fun_prop) _).clm_apply continuousOn_const
    intro z hz
    exact ⟨le_trans hz.1 hz.2.1, le_rfl, hz.2.2⟩

lemma remainderKernel_hasDerivAt {α T t s : ℝ} {k : ℝ × ℝ → 𝕜}
    (hk : SmoothAmplitude T k) (hz : (t,s) ∈ closedTriangle T) (hst : s < t) :
    HasDerivAt (fun x : ℝ => (x-s) ^ (α-1) • (k (x,s)-k (x,x)))
      ((t-s) ^ (α-1) • remainderDerivativeAmplitude α k (t,s)) t := by
  have hkt := (smoothAmplitude_hasFDerivAt hk hz).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))
  have hkd := (smoothAmplitude_hasFDerivAt hk
    (show (t,t) ∈ closedTriangle T from ⟨hz.1.trans hz.2.1, le_rfl, hz.2.2⟩)).comp_hasDerivAt (f := fun x : ℝ => (x,x)) t
      ((hasDerivAt_id t).prodMk (hasDerivAt_id t))
  have hbr : HasDerivAt (fun x : ℝ => k (x,s)-k (x,x))
      (fderiv ℝ k (t,s) (1,0)-fderiv ℝ k (t,t) (1,1)) t := by
    exact hkt.sub hkd
  have hp := ((hasDerivAt_id t).sub_const s).rpow_const
    (p := α-1) (Or.inl (sub_pos.mpr hst).ne')
  convert hp.smul hbr using 1
  · rfl
  symm
  change (t-s) ^ (α-1) • (fderiv ℝ k (t,s) (1,0)-fderiv ℝ k (t,t) (1,1)) +
    (1 * (α-1) * (t-s) ^ (α-1-1)) • (k (t,s)-k (t,t)) = _
  rw [amplitudeSlope_identity hk hz, smul_smul]
  have he : (t-s) ^ (α-1-1) * (t-s) = (t-s) ^ (α-1) := by
    rw [← Real.rpow_add_one (sub_pos.mpr hst).ne']
    congr 1
    ring
  rw [one_mul, mul_assoc, he]
  simp only [remainderDerivativeAmplitude, smul_add, smul_sub, smul_smul]
  module

lemma remainderKernel_eq {α T t s : ℝ} {k : ℝ × ℝ → 𝕜}
    (hα : 0 < α) (hk : SmoothAmplitude T k) (hz : (t,s) ∈ closedTriangle T) :
    (t-s) ^ (α-1) • (k (t,s)-k (t,t)) =
      (t-s) ^ α • amplitudeSlope k (t,s) := by
  rw [amplitudeSlope_identity hk hz, smul_smul]
  congr 1
  have h := Real.rpow_add_one' (sub_nonneg.mpr hz.2.1)
    (show α-1+1 ≠ 0 by linarith)
  simpa only [sub_add_cancel] using h.symm

lemma remainderKernel_continuousOn {α T t s : ℝ} {k : ℝ × ℝ → 𝕜}
    (hα : 0 < α) (hk : SmoothAmplitude T k) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ContinuousOn (fun x : ℝ => (x-s) ^ (α-1) • (k (x,s)-k (x,x))) (Icc s t) := by
  have hc : ContinuousOn (fun x : ℝ => (x-s)^α • amplitudeSlope k (x,s)) (Icc s t) := by
    apply ContinuousOn.smul
    · exact (continuousOn_id.sub continuousOn_const).rpow_const
        (fun x hx => Or.inr hα.le)
    · exact (amplitudeSlope_continuousOn hk).comp (by fun_prop)
        (fun x hx => ⟨hs,hx.1,hx.2.trans ht⟩)
  apply hc.congr
  intro x hx
  exact remainderKernel_eq hα hk ⟨hs,hx.1,hx.2.trans ht⟩

lemma forward_power_integrable {α s t : ℝ} (hα : 0 < α) :
    IntegrableOn (fun x : ℝ => (x-s) ^ (α-1)) (Ioc s t) := by
  have h := (intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := t-s) (by linarith : -1 < α-1)).comp_sub_right s
  simpa only [zero_add, sub_add_cancel] using h.1

lemma forward_weighted_integrable {α s t : ℝ} (hα : 0 < α)
    {g : ℝ → 𝕜} (hg : ContinuousOn g (Icc s t)) :
    IntegrableOn (fun x : ℝ => (x-s) ^ (α-1) • g x) (Ioc s t) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact (forward_power_integrable hα).smul_bdd C
    ((hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact hC x ⟨hx.1.le,hx.2⟩)

lemma remainderKernel_primitive {α T t s : ℝ} {k : ℝ × ℝ → 𝕜}
    (hα : 0 < α) (hk : SmoothAmplitude T k) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (∫ x in Ioc s t, (x-s) ^ (α-1) • remainderDerivativeAmplitude α k (x,s)) =
      (t-s) ^ (α-1) • (k (t,s)-k (t,t)) := by
  have hc : ContinuousOn (fun x : ℝ => remainderDerivativeAmplitude α k (x,s)) (Icc s t) :=
    (remainderDerivativeAmplitude_continuousOn hk).comp (by fun_prop)
      (fun x hx => ⟨hs,hx.1,hx.2.trans ht⟩)
  have hi := forward_weighted_integrable hα hc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (remainderKernel_continuousOn hα hk hs hst ht)
    (fun x hx => remainderKernel_hasDerivAt hk ⟨hs,hx.1.le,hx.2.le.trans ht⟩ hx.1)
    (show IntervalIntegrable
      (fun x : ℝ => (x-s) ^ (α-1) • remainderDerivativeAmplitude α k (x,s)) volume s t from
        ⟨hi, by simp [Ioc_eq_empty_of_le hst]⟩)
  simpa [intervalIntegral.integral_of_le hst] using hFTC

lemma remainder_contDiff_of_kernel_primitive {α T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    {k A : ℝ × ℝ → 𝕜} {f : ℝ → 𝕜}
    (hA : ContinuousOn A (closedTriangle T)) (hf : ContinuousOn f (Icc (0:ℝ) T))
    (hprim : ∀ t ∈ Icc (0:ℝ) T, ∀ s ∈ Icc (0:ℝ) t,
      (∫ x in Ioc s t, (x-s)^(α-1) • A (x,s)) =
        (t-s)^(α-1) • (k (t,s)-k (t,t))) :
    ContDiffOn ℝ 1 (remainderValue α k f) (Icc (0:ℝ) T) := by
  let D : ℝ → 𝕜 := amplitudeValue α A f
  have hD : ContinuousOn D (Icc (0:ℝ) T) := continuousOn_amplitudeValue hα hT hA hf
  apply contDiffOn_of_eq_integral hT hD
  intro t ht
  have hAf : ContinuousOn (fun z : ℝ × ℝ => A z * f z.2) (closedTriangle t) := by
    apply ContinuousOn.mul
    · exact hA.mono (fun z hz => ⟨hz.1,hz.2.1,hz.2.2.trans ht.2⟩)
    · exact hf.comp continuous_snd.continuousOn
        (fun z hz => ⟨hz.1,hz.2.1.trans (hz.2.2.trans ht.2)⟩)
  calc
    remainderValue α k f t =
      ∫ s in Ioc 0 t, (∫ x in Ioc s t, (x-s)^(α-1) • A (x,s)) * f s := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [hprim t ht s ⟨hs.1.le,hs.2⟩]
        exact (smul_mul_assoc ((t-s)^(α-1)) (k (t,s)-k (t,t)) (f s)).symm
    _ = ∫ s in Ioc 0 t, ∫ x in Ioc s t, (x-s)^(α-1) • (A (x,s)*f s) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      exact smul_mul_assoc ((x-s)^(α-1)) (A (x,s)) (f s)
    _ = ∫ x in Ioc 0 t, ∫ s in Ioc 0 x, (x-s)^(α-1) • (A (x,s)*f s) :=
      weighted_triangle_fubini hα hAf
    _ = ∫ x in Ioc 0 t, D x := rfl

/-- The explicit remainder is C¹ with only continuous input data. -/
theorem remainder_differentiability : RemainderDifferentiability := by
  intro 𝕜 _ α T hα hα1 hT k f hk hf
  apply remainder_contDiff_of_kernel_primitive hα hT
    (remainderDerivativeAmplitude_continuousOn hk) hf
  intro t ht s hs
  exact remainderKernel_primitive hα hk hs.1 hs.2 ht.2

/-- Exact decomposition and C¹ regularity of the unnormalized remainder. -/
theorem amplitude_remainder : AmplitudeRemainder :=
  remainder_assembly remainder_differentiability

/-- The original unnormalized smooth-amplitude integral gains α Hölder orders. -/
theorem amplitude_gain : AmplitudeGain :=
  gain_assembly fractional_gain amplitude_remainder

end ExpandedFA.PartV.FractionalHolder
