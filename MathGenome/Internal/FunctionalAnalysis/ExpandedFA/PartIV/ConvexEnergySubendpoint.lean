import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConvexEnergySubendpoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The subendpoint part of `fa2:p4:nemytskii-energy` (paper.tex:21449–21486).
The primitive and remainder are the canonical objects in the independent Specs.
The proof first obtains the Bregman L¹ limit, then uses scalar barriers and
subsequence extraction to establish convergence in measure. Restricted-measure
Hölder bounds and finite-measure Vitali give the whole-sequence Lq limits.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
universe u

namespace ExpandedFA.PartIV.ConvexEnergySubendpoint

open Spec

/-- Continuity of the primitive, including negative arguments and zero. -/
theorem primitive_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (primitive g) :=
  (intervalIntegral.differentiable_integral_of_continuous hg).continuous

/-- The remainder is the oriented integral of the difference from the base slope. -/
theorem remainder_eq_integral {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    remainder g a b = ∫ s in b..a, (g s - g b) := by
  unfold remainder primitive
  rw [intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), intervalIntegral.integral_sub
      (hg.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- On the left of the base point the signs of the integral and the slope reverse. -/
theorem remainder_eq_integral_left {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    remainder g a b = ∫ s in a..b, (g b - g s) := by
  rw [remainder_eq_integral hg, intervalIntegral.integral_symm]
  rw [← intervalIntegral.integral_neg]
  congr 1
  ext s
  ring

theorem remainder_nonnegative : Spec.RemainderNonnegative := by
  intro g hg hm a b
  rcases le_total b a with h | h
  · rw [remainder_eq_integral hg]
    exact intervalIntegral.integral_nonneg h (fun s hs => sub_nonneg.mpr (hm hs.1))
  · rw [remainder_eq_integral_left hg]
    exact intervalIntegral.integral_nonneg h (fun s hs => sub_nonneg.mpr (hm hs.2))

/-- On either side of the base point, moving away increases the remainder. -/
theorem remainder_mono_right {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g)
    {a b c : ℝ} (hbc : b ≤ c) (hca : c ≤ a) : remainder g c b ≤ remainder g a b := by
  rw [remainder_eq_integral hg, remainder_eq_integral hg]
  apply intervalIntegral.integral_mono_interval le_rfl hbc hca
  · exact (ae_restrict_mem measurableSet_Ioc).mono (fun s hs => sub_nonneg.mpr (hm hs.1.le))
  · exact (hg.sub continuous_const).intervalIntegrable _ _

theorem remainder_mono_left {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g)
    {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) : remainder g c b ≤ remainder g a b := by
  rw [remainder_eq_integral_left hg, remainder_eq_integral_left hg]
  apply intervalIntegral.integral_mono_interval hac hcb le_rfl
  · exact (ae_restrict_mem measurableSet_Ioc).mono (fun s hs => sub_nonneg.mpr (hm hs.2))
  · exact (continuous_const.sub hg).intervalIntegrable _ _

/-- Positive change of slope forces a positive remainder, even at a finite endpoint. -/
theorem remainder_pos_right {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g)
    {a b : ℝ} (h : g b < g a) : 0 < remainder g a b := by
  have hba : b < a := lt_of_not_ge (fun hab => not_le_of_gt h (hm hab))
  rw [remainder_eq_integral hg]
  apply intervalIntegral.integral_pos hba (hg.sub continuous_const).continuousOn
  · intro s hs
    exact sub_nonneg.mpr (hm hs.1.le)
  · exact ⟨a, ⟨hba.le, le_rfl⟩, sub_pos.mpr h⟩

theorem remainder_pos_left {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g)
    {a b : ℝ} (h : g a < g b) : 0 < remainder g a b := by
  have hab : a < b := lt_of_not_ge (fun hba => not_le_of_gt h (hm hba))
  rw [remainder_eq_integral_left hg]
  apply intervalIntegral.integral_pos hab (continuous_const.sub hg).continuousOn
  · intro s hs
    exact sub_nonneg.mpr (hm hs.2)
  · exact ⟨a, ⟨le_rfl, hab.le⟩, sub_pos.mpr h⟩

theorem eventually_lt_of_remainder_tendsto {g : ℝ → ℝ} (hg : Continuous g)
    (hm : Monotone g) {a : ℕ → ℝ} {b c : ℝ} (hbc : g b < g c)
    (ha : Tendsto (fun n => remainder g (a n) b) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, a n < c := by
  have hpos := remainder_pos_right hg hm hbc
  have hbc' : b ≤ c := (lt_of_not_ge (fun h => hbc.not_ge (hm h))).le
  filter_upwards [ha.eventually_lt_const hpos] with n hn
  exact lt_of_not_ge (fun h => hn.not_ge (remainder_mono_right hg hm hbc' h))

theorem eventually_gt_of_remainder_tendsto {g : ℝ → ℝ} (hg : Continuous g)
    (hm : Monotone g) {a : ℕ → ℝ} {b c : ℝ} (hcb : g c < g b)
    (ha : Tendsto (fun n => remainder g (a n) b) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, c < a n := by
  have hpos := remainder_pos_left hg hm hcb
  have hcb' : c ≤ b := (lt_of_not_ge (fun h => hcb.not_ge (hm h))).le
  filter_upwards [ha.eventually_lt_const hpos] with n hn
  exact lt_of_not_ge (fun h => hn.not_ge (remainder_mono_left hg hm h hcb'))

/-- No boundedness assumption on a scalar sequence is needed. Intermediate values
of the slope give barriers with positive remainder on either side. -/
theorem scalar_image_convergence : Spec.ScalarImageConvergence := by
  intro g hg hm a b ha
  apply tendsto_order.mpr
  constructor
  · intro y hy
    by_cases h : ∃ t : ℝ, g t ≤ y
    · obtain ⟨t, ht⟩ := h
      obtain ⟨c, hc⟩ := intermediate_value_univ t b hg
        (show (y + g b) / 2 ∈ Icc (g t) (g b) from ⟨by linarith, by linarith⟩)
      have hcb : g c < g b := by rw [hc]; linarith
      filter_upwards [eventually_gt_of_remainder_tendsto hg hm hcb ha] with n hn
      have := hm hn.le
      rw [hc] at this
      linarith
    · exact Eventually.of_forall (fun n => lt_of_not_ge (fun hn => h ⟨a n, hn⟩))
  · intro y hy
    by_cases h : ∃ t : ℝ, y ≤ g t
    · obtain ⟨t, ht⟩ := h
      obtain ⟨c, hc⟩ := intermediate_value_univ b t hg
        (show (g b + y) / 2 ∈ Icc (g b) (g t) from ⟨by linarith, by linarith⟩)
      have hbc : g b < g c := by rw [hc]; linarith
      filter_upwards [eventually_lt_of_remainder_tendsto hg hm hbc ha] with n hn
      have := hm hn.le
      rw [hc] at this
      linarith
    · exact Eventually.of_forall (fun n => lt_of_not_ge (fun hn => h ⟨a n, hn⟩))

theorem scalar_strict_convergence : Spec.ScalarStrictConvergence := by
  intro g hg hm a b ha
  exact tendsto_order.mpr
    ⟨fun c hc => eventually_gt_of_remainder_tendsto hg hm.monotone (hm hc) ha,
      fun c hc => eventually_lt_of_remainder_tendsto hg hm.monotone (hm hc) ha⟩

/-- Measurability of the remainder uses the original measurable representatives. -/
theorem remainder_aestronglyMeasurable {X : Type u} [MeasurableSpace X]
    {μ : Measure X} {g : ℝ → ℝ} (hg : Continuous g) {f h : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun x => remainder g (f x) (h x)) μ :=
  (((primitive_continuous hg).comp_aestronglyMeasurable hf).sub
    ((primitive_continuous hg).comp_aestronglyMeasurable hh)).sub
      ((hg.comp_aestronglyMeasurable hh).mul (hf.sub hh))

/-- Integral convergence for the nonnegative remainder is its L¹ convergence. -/
theorem remainder_norm_tendsto {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g) (f : ℕ → X → ℝ) (h : X → ℝ)
    (hi : ∀ n, Integrable (fun x => remainder g (f n x) (h x)) μ)
    (ht : Tendsto (fun n => ∫ x, remainder g (f n x) (h x) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => remainder g (f n x) (h x)) 1 μ)
      atTop (𝓝 0) := by
  have heq : ∀ n, eLpNorm (fun x => remainder g (f n x) (h x)) 1 μ =
      ENNReal.ofReal (∫ x, remainder g (f n x) (h x) ∂μ) := by
    intro n
    rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr (hi n))]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => Real.norm_of_nonneg (remainder_nonnegative g hg hm _ _))
  simp_rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp ht

/-- Every subsequence has a further subsequence on which the remainder tends to
zero a.e.; the scalar lemma then identifies the nonlinear image limit. -/
theorem image_inMeasure_of_remainder {X : Type u} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g)
    (f : ℕ → X → ℝ) (h : X → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hD : Tendsto (fun n => eLpNorm (fun x => remainder g (f n x) (h x)) 1 μ)
      atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n x => g (f n x)) atTop (fun x => g (h x)) := by
  have hDm : TendstoInMeasure μ (fun n x => remainder g (f n x) (h x))
      atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    change Tendsto (fun n => eLpNorm
      (fun x => remainder g (f n x) (h x) - 0) 1 μ) atTop (𝓝 0)
    simpa only [sub_zero] using hD
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => hg.comp_aestronglyMeasurable (hf n))).mpr
  intro r hr
  obtain ⟨s, hs, hds⟩ := (hDm.comp hr.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨s, hs, hds.mono ?_⟩
  intro x hx
  exact scalar_image_convergence g hg hm (fun n => f (r (s n)) x) (h x) hx

theorem strict_inMeasure_of_remainder {X : Type u} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {g : ℝ → ℝ} (hg : Continuous g) (hm : StrictMono g)
    (f : ℕ → X → ℝ) (h : X → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hD : Tendsto (fun n => eLpNorm (fun x => remainder g (f n x) (h x)) 1 μ)
      atTop (𝓝 0)) : TendstoInMeasure μ f atTop h := by
  have hDm : TendstoInMeasure μ (fun n x => remainder g (f n x) (h x))
      atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    change Tendsto (fun n => eLpNorm
      (fun x => remainder g (f n x) (h x) - 0) 1 μ) atTop (𝓝 0)
    simpa only [sub_zero] using hD
  apply (exists_seq_tendstoInMeasure_atTop_iff hf).mpr
  intro r hr
  obtain ⟨s, hs, hds⟩ := (hDm.comp hr.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨s, hs, hds.mono ?_⟩
  intro x hx
  exact scalar_strict_convergence g hg hm (fun n => f (r (s n)) x) (h x) hx

/-- A bound at a strictly larger finite exponent gives uniform integrability
at the lower exponent. The restricted-measure Hölder estimate supplies the
uniform modulus C δ^(1/q - 1/p). -/
theorem unifIntegrable_of_higher_bound {X : Type u} [MeasurableSpace X]
    {μ : Measure X} {p q : ℝ≥0∞} (hq : 0 < q) (hqp : q < p) (hp : p ≠ ∞)
    {f : ℕ → X → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ n, eLpNorm (f n) p μ ≤ C) :
    UnifIntegrable f q μ := by
  have hqtop : q ≠ ∞ := ne_top_of_lt hqp
  have hr : 0 < 1 / q.toReal - 1 / p.toReal := by
    have hqr := ENNReal.toReal_pos hq.ne' hqtop
    have hqpr := (ENNReal.toReal_lt_toReal hqtop hp).mpr hqp
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hqr hqpr)
  have ht := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hr
  apply unifIntegrable_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.nhds_zero_basis_Iic.eventually_iff.mp
    ((ENNReal.tendsto_nhds_zero.mp ht) ε hε)
  refine ⟨δ, hδ, fun n s hμs => ?_⟩
  calc
    eLpNorm (f n) q (μ.restrict s) ≤
        eLpNorm (f n) p (μ.restrict s) * (μ s) ^ (1 / q.toReal - 1 / p.toReal) := by
      simpa only [Measure.restrict_apply_univ] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp.le (hf n).restrict
    _ ≤ C * δ ^ (1 / q.toReal - 1 / p.toReal) := by
      apply mul_le_mul'
      · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hb n)
      · exact ENNReal.rpow_le_rpow hμs hr.le
    _ ≤ ε := hδε (mem_Iic.mpr le_rfl)

/-- Finite-measure Vitali, with its uniform-integrability hypothesis discharged
by a bound at a larger exponent. -/
theorem subendpoint_of_inMeasure_bound {X : Type u} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hq : 1 ≤ q)
    (hqp : q < p) (hp : p ≠ ∞) {f : ℕ → X → ℝ} {h : X → ℝ}
    (hf : ∀ n, MemLp (f n) p μ) (hh : MemLp h p μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ n, eLpNorm (f n) p μ ≤ C)
    (ht : TendstoInMeasure μ f atTop h) :
    (∀ n, MemLp (f n) q μ) ∧ MemLp h q μ ∧
      Tendsto (fun n => eLpNorm (f n - h) q μ) atTop (𝓝 0) := by
  have hfq : ∀ n, MemLp (f n) q μ := fun n => (hf n).mono_exponent hqp.le
  have hhq := hh.mono_exponent hqp.le
  refine ⟨hfq, hhq, tendsto_Lp_finite_of_tendstoInMeasure hq (ne_top_of_lt hqp)
    (fun n => (hf n).aestronglyMeasurable) hhq ?_ ht⟩
  exact unifIntegrable_of_higher_bound (zero_lt_one.trans_le hq) hqp hp
    (fun n => (hf n).aestronglyMeasurable) hC hb

/-- The conjugate exponent has the precise quotient needed for powers in Lp. -/
theorem toReal_gt_one {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞) : 1 < p.toReal := by
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).mpr hp

theorem conjugate_eq_div {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞) :
    conjugate p = p / ENNReal.ofReal (p.toReal - 1) := by
  rw [conjugate, ENNReal.ofReal_div_of_pos (sub_pos.mpr (toReal_gt_one hp hptop)),
    ENNReal.ofReal_toReal hptop]

theorem conjugate_holder {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞) :
    ENNReal.HolderConjugate p (conjugate p) := by
  have h := (Real.HolderConjugate.conjExponent (toReal_gt_one hp hptop)).ennrealOfReal
  simpa only [Real.conjExponent, ENNReal.ofReal_toReal hptop, conjugate] using h

theorem conjugate_gt_one {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞) :
    1 < conjugate p := (conjugate_holder hp hptop).lt_top_iff_one_lt.mp (lt_top_iff_ne_top.mpr hptop)

theorem conjugate_ne_top (p : ℝ≥0∞) : conjugate p ≠ ∞ := ENNReal.ofReal_ne_top

/-- The upper-growth majorant belongs to the exact conjugate Lp space. -/
theorem image_memLp {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞) {g : ℝ → ℝ}
    (hg : Continuous g) (hgrowth : UpperGrowth p g) {f : X → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => g (f x)) (conjugate p) μ := by
  obtain ⟨C, _hC, hC⟩ := hgrowth
  have hr := sub_pos.mpr (toReal_gt_one hp hptop)
  have hpow : MemLp (fun x => |f x| ^ (p.toReal - 1)) (conjugate p) μ := by
    rw [conjugate_eq_div hp hptop]
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hr.le] using
      hf.norm_rpow_div (ENNReal.ofReal (p.toReal - 1))
  exact (((memLp_const (1 : ℝ)).add hpow).const_mul C).mono'
    (hg.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, Pi.add_apply] using hC (f x)))

/-- A monotone function on the interval from zero to t is bounded by its two
endpoint magnitudes. This avoids differentiability or strictness of g. -/
theorem primitive_abs_le {g : ℝ → ℝ} (hm : Monotone g) (t : ℝ) :
    |primitive g t| ≤ |t| * (|g 0| + |g t|) := by
  have hbound : ∀ s ∈ Set.uIoc 0 t, ‖g s‖ ≤ |g 0| + |g t| := by
    intro s hs
    have hs' := uIoc_subset_uIcc hs
    rcases mem_uIcc.mp hs' with hs' | hs'
    · have h := abs_le_max_abs_abs (hm hs'.1) (hm hs'.2)
      exact h.trans (max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _)))
    · have h := abs_le_max_abs_abs (hm hs'.1) (hm hs'.2)
      exact h.trans (max_le (le_add_of_nonneg_left (abs_nonneg _))
        (le_add_of_nonneg_right (abs_nonneg _)))
  simpa only [primitive, Real.norm_eq_abs, sub_zero, mul_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Monotonicity, upper growth and Hölder make the primitive integrable. -/
theorem primitive_integrable {X : Type u} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞)
    {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g) (hgrowth : UpperGrowth p g)
    {f : X → ℝ} (hf : MemLp f p μ) : Integrable (fun x => primitive g (f x)) μ := by
  haveI := conjugate_holder hp hptop
  have hgf := image_memLp hp hptop hg hgrowth hf
  have hi := hf.norm.integrable_mul ((memLp_const |g 0|).add hgf.norm)
  apply hi.mono' ((primitive_continuous hg).comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply] using primitive_abs_le hm (f x))

/-- Quantitative boundedness of the nonlinear image on Lp-bounded sets. -/
theorem image_eLpNorm_le {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞) {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ t, |g t| ≤ C * (1 + |t| ^ (p.toReal - 1)))
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ≥0∞}
    (hM : eLpNorm f p μ ≤ M) :
    eLpNorm (fun x => g (f x)) (conjugate p) μ ≤
      ‖C‖ₑ * (eLpNorm (fun _ : X => (1 : ℝ)) (conjugate p) μ + M ^ (p.toReal - 1)) := by
  have hr := sub_pos.mpr (toReal_gt_one hp hptop)
  have hexp : conjugate p * ENNReal.ofReal (p.toReal - 1) = p := by
    rw [conjugate_eq_div hp hptop]
    exact ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
  calc
    eLpNorm (fun x => g (f x)) (conjugate p) μ ≤
        eLpNorm (C • (fun x => 1 + |f x| ^ (p.toReal - 1))) (conjugate p) μ := by
      exact eLpNorm_mono_real (hg.comp_aestronglyMeasurable hf) (fun x => hC (f x))
    _ = ‖C‖ₑ * eLpNorm (fun x => 1 + |f x| ^ (p.toReal - 1)) (conjugate p) μ :=
      eLpNorm_const_smul _ _ _ _
    _ ≤ ‖C‖ₑ * (eLpNorm (fun _ : X => (1 : ℝ)) (conjugate p) μ +
        eLpNorm (fun x => |f x| ^ (p.toReal - 1)) (conjugate p) μ) := by
      exact mul_le_mul' le_rfl (eLpNorm_add_le (conjugate_gt_one hp hptop).le)
    _ ≤ ‖C‖ₑ * (eLpNorm (fun _ : X => (1 : ℝ)) (conjugate p) μ + M ^ (p.toReal - 1)) := by
      gcongr
      simp_rw [← Real.norm_eq_abs]
      rw [eLpNorm_norm_rpow f hf hr, hexp]
      exact ENNReal.rpow_le_rpow hM hr.le

/-- A single finite bound for the original sequence gives a single finite bound
for its nonlinear image at the conjugate exponent. -/
theorem image_uniform_bound {X : Type u} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞)
    {g : ℝ → ℝ} (hg : Continuous g) (hgrowth : UpperGrowth p g)
    {f : ℕ → X → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {M : ℝ≥0∞} (hMtop : M ≠ ∞) (hM : ∀ n, eLpNorm (f n) p μ ≤ M) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n, eLpNorm (fun x => g (f n x)) (conjugate p) μ ≤ K := by
  obtain ⟨C, _hC, hC⟩ := hgrowth
  refine ⟨_, ?_, fun n => image_eLpNorm_le hp hptop hg hC (hf n) (hM n)⟩
  apply ENNReal.mul_ne_top enorm_ne_top
  apply ENNReal.add_ne_top.mpr
  refine ⟨(memLp_const (1 : ℝ) (p := conjugate p) (μ := μ)).eLpNorm_ne_top, ?_⟩
  exact (ENNReal.rpow_lt_top_of_nonneg (sub_pos.mpr (toReal_gt_one hp hptop)).le hMtop).ne

/-- The same bounds control the energy integrals, so the real limsup in the
source is used only for an actually bounded sequence. -/
theorem primitive_uniform_bound {X : Type u} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ∞)
    {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g)
    {f : ℕ → X → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {M K : ℝ≥0∞} (hMtop : M ≠ ∞) (hKtop : K ≠ ∞)
    (hM : ∀ n, eLpNorm (f n) p μ ≤ M)
    (hK : ∀ n, eLpNorm (fun x => g (f n x)) (conjugate p) μ ≤ K) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ n, eLpNorm (fun x => primitive g (f n x)) 1 μ ≤ B := by
  haveI := conjugate_holder hp hptop
  let A := eLpNorm (fun _ : X => |g 0|) (conjugate p) μ
  refine ⟨M * (A + K), ENNReal.mul_ne_top hMtop
    (ENNReal.add_ne_top.mpr ⟨(memLp_const |g 0|).eLpNorm_ne_top, hKtop⟩), fun n => ?_⟩
  calc
    eLpNorm (fun x => primitive g (f n x)) 1 μ ≤
        eLpNorm ((fun x => |f n x|) • (fun x => |g 0| + |g (f n x)|)) 1 μ := by
      exact eLpNorm_mono_real
        ((primitive_continuous hg).comp_aestronglyMeasurable (hf n))
        (fun x => primitive_abs_le hm _)
    _ ≤ eLpNorm (fun x => |f n x|) p μ *
        eLpNorm (fun x => |g 0| + |g (f n x)|) (conjugate p) μ :=
      eLpNorm_smul_le_mul_eLpNorm_of_pos zero_lt_one
    _ ≤ eLpNorm (f n) p μ * (A + eLpNorm (fun x => g (f n x)) (conjugate p) μ) := by
      simp only [← Real.norm_eq_abs, eLpNorm_norm _ (hf n)]
      apply mul_le_mul' le_rfl
      have ht := eLpNorm_add_le (f := fun _ : X => ‖g 0‖)
        (g := fun x => ‖g (f n x)‖) (μ := μ) (conjugate_gt_one hp hptop).le
      change eLpNorm (fun x => ‖g 0‖ + ‖g (f n x)‖) (conjugate p) μ ≤
        A + eLpNorm (fun x => ‖g (f n x)‖) (conjugate p) μ at ht
      rw [eLpNorm_norm _ (hg.comp_aestronglyMeasurable (hf n))] at ht
      exact ht
    _ ≤ M * (A + K) := mul_le_mul' (hM n) (add_le_add le_rfl (hK n))

theorem growth_integrability : Spec.GrowthIntegrability.{u} := by
  intro X _ μ _ p _ hp hptop g hg hm hgr f
  exact ⟨image_memLp hp hptop hg hgr (Lp.memLp f),
    primitive_integrable hp hptop hg hm hgr (Lp.memLp f)⟩

/-- Weak convergence gives a finite bound in the original Lp norm. -/
theorem weak_uniform_bound {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : ℕ → Lp ℝ p μ} {u : Lp ℝ p μ}
    (hw : Spec.WeaklyConverges μ p v u) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (v n) p μ ≤ M := by
  obtain ⟨C, hC, hb⟩ := ExpandedFA.P1.C12BoundedSequences.norm_bound_of_scalar_bounds
    ℝ (Lp ℝ p μ) ℕ v (by
      intro L
      obtain ⟨B, hB⟩ := (hw L).norm.bddAbove_range
      exact ⟨B, fun n => hB (mem_range_self n)⟩)
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n => ?_⟩
  rw [← Lp.enorm_def]
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hb n)

/-- A nonnegative difference between the energy and an asymptotically vanishing
linear term tends to zero under the energy limsup inequality. -/
theorem tendsto_remainder_of_limsup {e l d : ℕ → ℝ} {e₀ : ℝ}
    (he : BddAbove (range e)) (hsup : limsup e atTop ≤ e₀)
    (hl : Tendsto l atTop (𝓝 0)) (hd : ∀ n, d n = e n - e₀ - l n)
    (hnonneg : ∀ n, 0 ≤ d n) : Tendsto d atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro y hy
    exact Eventually.of_forall (fun n => hy.trans_le (hnonneg n))
  · intro y hy
    have hevent : ∀ᶠ n in atTop, e n < e₀ + y / 2 :=
      eventually_lt_of_limsup_lt (hsup.trans_lt (by linarith)) he.isBoundedUnder_of_range
    filter_upwards [hevent, hl.eventually_const_lt (show -y / 2 < 0 by linarith)] with n hn hn'
    rw [hd]
    linarith

/-- Boundedness of the real energy sequence follows from the already established
Lp controls, rather than being added to the source hypotheses. -/
theorem energy_bddAbove {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {g : ℝ → ℝ} (hg : Continuous g) {f : ℕ → X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hb : ∀ n, eLpNorm (fun x => primitive g (f n x)) 1 μ ≤ B) :
    BddAbove (range (fun n => ∫ x, primitive g (f n x) ∂μ)) := by
  refine ⟨B.toReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  apply (le_abs_self _).trans
  apply (ENNReal.ofReal_le_iff_le_toReal hB).mp
  rw [← Real.norm_eq_abs, ofReal_norm]
  apply le_trans (enorm_integral_le_lintegral_enorm _)
  rw [← eLpNorm_one_eq_lintegral_enorm
    ((primitive_continuous hg).comp_aestronglyMeasurable (hf n))]
  exact hb n

/-- The weak pairing at the fixed slope g(u) is the linear term in the
Bregman identity; its convergence and the energy limsup force the remainder. -/
theorem remainder_convergence : Spec.RemainderConvergence.{u} := by
  intro X _ μ _ p _ g v u h
  obtain ⟨hp, hptop, hg, hm, hgr, hw, hsup⟩ := h
  haveI := conjugate_holder hp hptop
  haveI : Fact (1 ≤ conjugate p) := ⟨(conjugate_gt_one hp hptop).le⟩
  have hgu := image_memLp hp hptop hg hgr (Lp.memLp u)
  have hiE : ∀ n, Integrable (fun x => primitive g (v n x)) μ :=
    fun n => primitive_integrable hp hptop hg hm hgr (Lp.memLp (v n))
  have hiU := primitive_integrable hp hptop hg hm hgr (Lp.memLp u)
  let l : ℕ → ℝ := fun n => ∫ x, g (u x) * (v n x - u x) ∂μ
  have hli : ∀ n, Integrable (fun x => g (u x) * (v n x - u x)) μ := by
    intro n
    have hi := ((Lp.memLp (v n)).sub (Lp.memLp u)).integrable_mul hgu
    change Integrable (fun x => (v n x - u x) * g (u x)) μ at hi
    simpa only [mul_comm] using hi
  let guLp : Lp ℝ (conjugate p) μ := hgu.toLp (fun x => g (u x))
  let L := ExpandedFA.FunctionSpaces.lpIntegralPairing μ p (conjugate p) guLp
  have hL : ∀ f : Lp ℝ p μ, L f = ∫ x, f x * g (u x) ∂μ := by
    intro f
    calc
      L f = ∫ x, f x * guLp x ∂μ :=
        (ExpandedFA.FunctionSpaces.lp_pairing_integral μ p (conjugate p) guLp f).2
      _ = _ := integral_congr_ae (hgu.coeFn_toLp.mono (fun x hx => congrArg (fun t => f x * t) hx))
  have hl : Tendsto l atTop (𝓝 0) := by
    have heq : ∀ n, l n = L (v n) - L u := by
      intro n
      rw [hL, hL]
      calc
        l n = ∫ x, v n x * g (u x) - u x * g (u x) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun x => by dsimp [l]; ring)
        _ = _ := integral_sub ((Lp.memLp (v n)).integrable_mul hgu)
          ((Lp.memLp u).integrable_mul hgu)
    simp_rw [show l = fun n => L (v n) - L u from funext heq]
    simpa only [sub_self] using (hw L).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => L u) atTop (𝓝 (L u)))
  have hiD : ∀ n, Integrable (fun x => remainder g (v n x) (u x)) μ := by
    intro n
    exact ((hiE n).sub hiU).sub (hli n)
  obtain ⟨M, hM, hbM⟩ := weak_uniform_bound hw
  obtain ⟨K, hK, hbK⟩ := image_uniform_bound hp hptop hg hgr
    (fun n => Lp.aestronglyMeasurable (v n)) hM hbM
  obtain ⟨B, hB, hbB⟩ := primitive_uniform_bound hp hptop hg hm
    (fun n => Lp.aestronglyMeasurable (v n)) hM hK hbM hbK
  have hbE := energy_bddAbove hg (fun n => Lp.aestronglyMeasurable (v n)) hB hbB
  have ht : Tendsto (fun n => ∫ x, remainder g (v n x) (u x) ∂μ) atTop (𝓝 0) := by
    apply tendsto_remainder_of_limsup hbE hsup hl
    · intro n
      exact (integral_sub ((hiE n).sub hiU) (hli n)).trans
        (congrArg (fun z : ℝ => z - l n) (integral_sub (hiE n) hiU))
    · intro n
      exact integral_nonneg (fun x => remainder_nonnegative g hg hm _ _)
  exact ⟨hiD, ht, remainder_norm_tendsto hg hm _ _ hiD ht⟩

theorem image_subendpoint : Spec.ImageSubendpoint.{u} := by
  intro X _ μ _ p _ g v u h
  have hD := (remainder_convergence μ p g v u h).2.2
  obtain ⟨hp, hptop, hg, hm, hgr, hw, _⟩ := h
  have hmeasure := image_inMeasure_of_remainder hg hm
    (fun n x => v n x) (fun x => u x) (fun n => Lp.aestronglyMeasurable (v n)) hD
  refine ⟨hmeasure, fun q hq hqp => ?_⟩
  obtain ⟨M, hM, hbM⟩ := weak_uniform_bound hw
  obtain ⟨K, hK, hbK⟩ := image_uniform_bound hp hptop hg hgr
    (fun n => Lp.aestronglyMeasurable (v n)) hM hbM
  exact subendpoint_of_inMeasure_bound hq hqp (conjugate_ne_top p)
    (fun n => image_memLp hp hptop hg hgr (Lp.memLp (v n)))
    (image_memLp hp hptop hg hgr (Lp.memLp u)) hK hbK hmeasure

theorem strict_subendpoint : Spec.StrictSubendpoint.{u} := by
  intro X _ μ _ p _ g v u h hstrict
  have hD := (remainder_convergence μ p g v u h).2.2
  obtain ⟨hp, hptop, hg, _hm, _hgr, hw, _⟩ := h
  have hmeasure := strict_inMeasure_of_remainder hg hstrict
    (fun n x => v n x) (fun x => u x) (fun n => Lp.aestronglyMeasurable (v n)) hD
  refine ⟨hmeasure, fun q hq hqp => ?_⟩
  obtain ⟨M, hM, hbM⟩ := weak_uniform_bound hw
  exact subendpoint_of_inMeasure_bound hq hqp hptop
    (fun n => Lp.memLp (v n)) (Lp.memLp u) hM hbM hmeasure

end ExpandedFA.PartIV.ConvexEnergySubendpoint
