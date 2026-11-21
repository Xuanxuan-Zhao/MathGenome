import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Interpolation.RieszThorin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.ThreeLines
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Basic.Real.ConjExponents
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.Holder
import MathGenome.RealAnalysis.Topics.D11.Ch20
import MathGenome.Internal.RealAnalysis.D11.Ch11.BoundedSimpleInfinity

noncomputable section
open MeasureTheory
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.Interpolation
open RieszThorinSpec

/-- Hölder applied to the positive powers 1-θ and θ of the same modulus.
This proof includes all infinity configurations and uses no convolution bound. -/
theorem lp_norm_interpolation : NormInterpolation.{u} := by
  intro X _ μ r₀ r₁ r θ hθ₀ hθ₁ hr f hf
  have ha : 0 < 1 - θ := sub_pos.mpr hθ₁
  have ha0 : ENNReal.ofReal (1 - θ) ≠ 0 := by positivity
  have hb0 : ENNReal.ofReal θ ≠ 0 := by positivity
  have hholder : ENNReal.HolderTriple
      (r₀ / ENNReal.ofReal (1 - θ)) (r₁ / ENNReal.ofReal θ) r := by
    constructor
    rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl ha0),
      ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hb0)]
    exact hr.symm
  have := hholder
  have heq : (fun x => ‖f x‖ₑ) =
      (fun x => ‖f x‖ₑ ^ (1 - θ)) * (fun x => ‖f x‖ₑ ^ θ) := by
    funext x
    simp only [Pi.mul_apply, ← ENNReal.rpow_add_of_nonneg _ _ ha.le hθ₀.le, sub_add_cancel,
      ENNReal.rpow_one]
  rw [← eLpNorm_enorm f hf, heq]
  calc
    _ ≤ eLpNorm (fun x => ‖f x‖ₑ ^ (1 - θ))
        (r₀ / ENNReal.ofReal (1 - θ)) μ *
        eLpNorm (fun x => ‖f x‖ₑ ^ θ) (r₁ / ENNReal.ofReal θ) μ :=
      eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal (by fun_prop) (by fun_prop)
    _ = _ := by
      rw [eLpNorm_enorm_rpow f hf ha, eLpNorm_enorm_rpow f hf hθ₀,
        ENNReal.div_mul_cancel ha0 ENNReal.ofReal_ne_top,
        ENNReal.div_mul_cancel hb0 ENNReal.ofReal_ne_top]

/-- Convert two bounds on the same measurable output to the geometric bound.
No strictly positive operator constant or input norm is required. -/
theorem interpolate_output_bounds {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (r₀ r₁ r : ℝ≥0∞) (θ M₀ M₁ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hr : Interpolates r₀ r₁ r θ) (g : X → ℂ)
    (hg : AEStronglyMeasurable g μ) (N : ℝ≥0∞)
    (h₀ : eLpNorm g r₀ μ ≤ ENNReal.ofReal M₀ * N)
    (h₁ : eLpNorm g r₁ μ ≤ ENNReal.ofReal M₁ * N) :
    eLpNorm g r μ ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * N := by
  have ha : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁.le
  calc
    eLpNorm g r μ ≤ eLpNorm g r₀ μ ^ (1 - θ) * eLpNorm g r₁ μ ^ θ :=
      lp_norm_interpolation μ r₀ r₁ r θ hθ₀ hθ₁ hr g hg
    _ ≤ (ENNReal.ofReal M₀ * N) ^ (1 - θ) * (ENNReal.ofReal M₁ * N) ^ θ :=
      mul_le_mul' (ENNReal.rpow_le_rpow h₀ ha) (ENNReal.rpow_le_rpow h₁ hθ₀.le)
    _ = ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * N := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.mul_rpow_of_nonneg _ _ hθ₀.le,
        mul_mul_mul_comm,
        ← ENNReal.rpow_add_of_nonneg _ _ ha hθ₀.le,
        sub_add_cancel, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg hM₀ ha,
        ENNReal.ofReal_rpow_of_nonneg hM₁ hθ₀.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hM₀ _)]

/-- The infinite-domain endpoint follows from scalar norm interpolation on Tf. -/
theorem riesz_thorin_infinity_domain : InfinityDomain.{u,v} := by
  intro X Y _ _ μ ν q₀ q₁ q θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hq T h₀ h₁ f
  have hf : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ ∞ ∞ :=
    Submodule.mem_sup_left (show (f : X →ₘ[μ] ℂ) ∈ Lp.LpSubmodule ℂ ℂ ∞ μ from f.property)
  let F : SumSpace μ ∞ ∞ := ⟨f, hf⟩
  have hF : MemLp (F : X →ₘ[μ] ℂ) ∞ μ := Lp.memLp f
  have hbound := interpolate_output_bounds ν q₀ q₁ q θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hq
    (T F) (T F).aestronglyMeasurable (eLpNorm f ∞ μ) (h₀ F hF).2 (h₁ F hF).2
  have hfinite : ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f ∞ μ < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)
  refine ⟨hf, hbound.trans_lt hfinite, ?_⟩
  have hreal := ENNReal.toReal_mono hfinite.ne hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ), ← Lp.norm_def] using hreal

/-- An interior parameter gives p=∞ only when both original exponents are ∞. -/
theorem interpolates_top_iff (p₀ p₁ : ℝ≥0∞) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    Interpolates p₀ p₁ ∞ θ ↔ p₀ = ∞ ∧ p₁ = ∞ := by
  have ha : ENNReal.ofReal (1 - θ) ≠ 0 := by positivity
  have hb : ENNReal.ofReal θ ≠ 0 := by positivity
  simp [Interpolates, eq_comm (a := (0 : ℝ≥0∞)), ha, hb,
    ENNReal.inv_eq_zero]

/-- Truncation below one upgrades a finite-p function to any larger exponent,
including infinity, on an arbitrary measure space. -/
theorem memLp_small_part {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p r : ℝ≥0∞) (f : X → ℂ)
    (hp₀ : p ≠ 0) (hpt : p ≠ ∞) (hpr : p ≤ r) (hf : MemLp f p μ) :
    MemLp ({x | ‖f x‖ₑ ≤ 1}.indicator f) r μ := by
  let S := {x | ‖f x‖ₑ ≤ 1}
  have hS : NullMeasurableSet S μ :=
    hf.aestronglyMeasurable.enorm.aestronglyMeasurable.nullMeasurableSet_le
      aestronglyMeasurable_const
  have hmeas := hf.aestronglyMeasurable.indicator₀ hS
  by_cases hrt : r = ∞
  · subst r
    apply memLp_top_of_bound_enorm hmeas 1
    filter_upwards with x
    by_cases hx : x ∈ S
    · simpa only [Set.indicator_of_mem hx, ENNReal.coe_one] using (show ‖f x‖ₑ ≤ 1 from hx)
    · simp [Set.indicator_of_notMem hx]
  have hr₀ : r ≠ 0 := ne_of_gt ((bot_lt_iff_ne_bot.mpr hp₀).trans_le hpr)
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hr₀ hrt hmeas]
  refine (lintegral_mono fun x => ?_).trans_lt
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hpt hf)
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hx (ENNReal.toReal_mono hrt hpr)
  · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hr₀ hrt)]

/-- The native Lp class belongs to the actual algebraic sum whenever its
exponent lies between the two domain exponents. This is a domain theorem,
not an assumed embedding. -/
theorem lp_mem_sum_of_between {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    (hp₀ : p ≠ 0) (hpt : p ≠ ∞) (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (f : Lp ℂ p μ) : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ p₀ p₁ := by
  let S := {x | ‖f x‖ₑ ≤ 1}
  have hS : NullMeasurableSet S μ :=
    (Lp.aestronglyMeasurable f).enorm.aestronglyMeasurable.nullMeasurableSet_le
      aestronglyMeasurable_const
  have hsmall : MemLp (S.indicator (f : X → ℂ)) p₁ μ :=
    memLp_small_part μ p p₁ f hp₀ hpt h₁ (Lp.memLp f)
  have hlarge : MemLp (Sᶜ.indicator (f : X → ℂ)) p μ :=
    (Lp.memLp f).indicator hS.compl
  have hsupp : μ (Function.support (Sᶜ.indicator (f : X → ℂ))) < ∞ := by
    apply lt_of_le_of_lt (measure_mono ?_)
      ((Lp.memLp f).meas_ge_lt_top'_enorm hp₀ hpt (by simp : (1 : ℝ≥0∞) ≠ 0)
        (by simp))
    intro x hx
    have hxS : x ∉ S := by
      intro h
      exact hx (by simp [Set.indicator_of_notMem (show x ∉ Sᶜ from fun hx => hx h)])
    exact (lt_of_not_ge (show ¬ ‖f x‖ₑ ≤ 1 from hxS)).le
  have hlarge₀ : MemLp (Sᶜ.indicator (f : X → ℂ)) p₀ μ :=
    hlarge.mono_exponent_of_measure_support_ne_top
      (fun x hx => Function.notMem_support.mp hx) hsupp.ne h₀
  apply Submodule.mem_sup.mpr
  refine ⟨AEEqFun.mk _ hlarge₀.aestronglyMeasurable, ?_,
    AEEqFun.mk _ hsmall.aestronglyMeasurable, ?_, ?_⟩
  · exact Lp.mem_Lp_iff_memLp.mpr (hlarge₀.ae_eq (AEEqFun.coeFn_mk _ _).symm)
  · exact Lp.mem_Lp_iff_memLp.mpr (hsmall.ae_eq (AEEqFun.coeFn_mk _ _).symm)
  · apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_add
      (AEEqFun.mk _ hlarge₀.aestronglyMeasurable)
      (AEEqFun.mk _ hsmall.aestronglyMeasurable),
      AEEqFun.coeFn_mk _ hlarge₀.aestronglyMeasurable,
      AEEqFun.coeFn_mk _ hsmall.aestronglyMeasurable] with x hsum hl hs
    rw [hsum, Pi.add_apply, hl, hs]
    by_cases hx : x ∈ S <;> simp [hx]

/-- Convex reciprocal interpolation places the exponent between ordered endpoints. -/
theorem interpolates_between (p₀ p₁ p : ℝ≥0∞) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : Interpolates p₀ p₁ p θ)
    (horder : p₀ ≤ p₁) : p₀ ≤ p ∧ p ≤ p₁ := by
  have ha : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁.le
  have hweights : ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_add ha hθ₀.le, sub_add_cancel, ENNReal.ofReal_one]
  constructor
  · apply ENNReal.inv_le_inv.mp
    calc
      p⁻¹ = _ := hp
      _ ≤ ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₀⁻¹ :=
        add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr horder))
      _ = p₀⁻¹ := by rw [← add_mul, hweights, one_mul]
  · apply ENNReal.inv_le_inv.mp
    calc
      p₁⁻¹ = (ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ) * p₁⁻¹ := by
        rw [hweights, one_mul]
      _ ≤ ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹ := by
        rw [add_mul]
        exact add_le_add (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr horder)) le_rfl
      _ = p⁻¹ := hp.symm

/-- Every intermediate Lp function can actually be passed to the original T. -/
theorem lp_mem_interpolation_sum : IntermediateDomain.{u} := by
  intro X _ μ p₀ p₁ p θ hθ₀ hθ₁ hp₀ hp f
  by_cases hpt : p = ∞
  · subst p
    obtain ⟨rfl, rfl⟩ := (interpolates_top_iff _ _ _ hθ₀ hθ₁).mp hp
    exact Submodule.mem_sup_left f.property
  rcases le_total p₀ p₁ with horder | horder
  · obtain ⟨h₀, h₁⟩ := interpolates_between _ _ _ θ hθ₀ hθ₁ hp horder
    exact lp_mem_sum_of_between μ p₀ p₁ p hp₀ hpt h₀ h₁ f
  · have hswap : Interpolates p₁ p₀ p (1 - θ) := by
      have heq : 1 - (1 - θ) = θ := by ring
      simp only [Interpolates, heq, add_comm] at hp ⊢
      exact hp
    obtain ⟨h₀, h₁⟩ := interpolates_between p₁ p₀ p (1 - θ)
      (sub_pos.mpr hθ₁) (by linarith) hswap horder
    simpa only [SumSpace, sup_comm] using
      lp_mem_sum_of_between μ p₁ p₀ p hp₀ hpt h₀ h₁ f

/-- The unit ball of an intermediate Lp space lies in the sum of the two
endpoint unit balls. This quantitative decomposition controls the original
common-domain operator during a density argument. -/
theorem lp_unit_decomposition {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    (hpt : p ≠ ∞) (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (f : Lp ℂ p μ) (hf : ‖f‖ ≤ 1) :
    ∃ a : Lp ℂ p₀ μ, ∃ b : Lp ℂ p₁ μ,
      (a : X →ₘ[μ] ℂ) + (b : X →ₘ[μ] ℂ) = (f : X →ₘ[μ] ℂ) ∧
        ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp₀z : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₀t : p₀ ≠ ∞ := ne_top_of_le_ne_top hpt h₀
  have hnorm : eLpNorm f p μ ≤ 1 := by
    rw [← Lp.enorm_def, enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_le_coe]
    exact hf
  have hint : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≤ 1 := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hpz hpt),
      ← eLpNorm_eq_eLpNorm' hpz hpt (Lp.aestronglyMeasurable f)]
    exact (ENNReal.rpow_le_rpow hnorm ENNReal.toReal_nonneg).trans_eq (by simp)
  let S := {x | ‖f x‖ₑ ≤ 1}
  have hS : NullMeasurableSet S μ :=
    (Lp.aestronglyMeasurable f).enorm.aestronglyMeasurable.nullMeasurableSet_le
      aestronglyMeasurable_const
  have hlarge : AEStronglyMeasurable (Sᶜ.indicator (f : X → ℂ)) μ :=
    (Lp.aestronglyMeasurable f).indicator₀ hS.compl
  have hsmall : AEStronglyMeasurable (S.indicator (f : X → ℂ)) μ :=
    (Lp.aestronglyMeasurable f).indicator₀ hS
  have hA : eLpNorm (Sᶜ.indicator (f : X → ℂ)) p₀ μ ≤ 1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀z hp₀t hlarge]
    suffices (∫⁻ x, ‖Sᶜ.indicator (f : X → ℂ) x‖ₑ ^ p₀.toReal ∂μ) ≤ 1 by
      exact (ENNReal.rpow_le_rpow this (by positivity)).trans_eq (by simp)
    apply le_trans (lintegral_mono fun x => ?_) hint
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_notMem (show x ∉ Sᶜ from fun h => h hx),
        ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp₀z hp₀t)]
    · rw [Set.indicator_of_mem (show x ∈ Sᶜ from hx)]
      exact ENNReal.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx))
        (ENNReal.toReal_mono hpt h₀)
  have hB : eLpNorm (S.indicator (f : X → ℂ)) p₁ μ ≤ 1 := by
    by_cases hp₁t : p₁ = ∞
    · rw [hp₁t, eLpNorm_exponent_top hsmall]
      apply eLpNormEssSup_le_of_ae_enorm_bound
      filter_upwards with x
      by_cases hx : x ∈ S
      · simpa only [Set.indicator_of_mem hx] using (show ‖f x‖ₑ ≤ 1 from hx)
      · simp [Set.indicator_of_notMem hx]
    have hp₁z : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₁z hp₁t hsmall]
    suffices (∫⁻ x, ‖S.indicator (f : X → ℂ) x‖ₑ ^ p₁.toReal ∂μ) ≤ 1 by
      exact (ENNReal.rpow_le_rpow this (by positivity)).trans_eq (by simp)
    apply le_trans (lintegral_mono fun x => ?_) hint
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.rpow_le_rpow_of_exponent_ge hx (ENNReal.toReal_mono hp₁t h₁)
    · simp [Set.indicator_of_notMem hx,
        ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp₁z hp₁t)]
  have hAmem : MemLp (Sᶜ.indicator (f : X → ℂ)) p₀ μ := hA.trans_lt (by simp)
  have hBmem : MemLp (S.indicator (f : X → ℂ)) p₁ μ := hB.trans_lt (by simp)
  refine ⟨hAmem.toLp _, hBmem.toLp _, ?_, ?_, ?_⟩
  · apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_add
      (hAmem.toLp _ : X →ₘ[μ] ℂ) (hBmem.toLp _ : X →ₘ[μ] ℂ),
      hAmem.coeFn_toLp, hBmem.coeFn_toLp] with x hsum ha hb
    rw [hsum, Pi.add_apply, ha, hb]
    by_cases hx : x ∈ S <;> simp [hx]
  · rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hA).trans_eq (by simp)
  · rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hB).trans_eq (by simp)

/-- Every intermediate Lp vector has an endpoint decomposition whose two
norms are at most its own norm. No finite total measure is assumed. -/
theorem lp_norm_decomposition {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    (hpt : p ≠ ∞) (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (f : Lp ℂ p μ) :
    ∃ a : Lp ℂ p₀ μ, ∃ b : Lp ℂ p₁ μ,
      (a : X →ₘ[μ] ℂ) + (b : X →ₘ[μ] ℂ) = (f : X →ₘ[μ] ℂ) ∧
        ‖a‖ ≤ ‖f‖ ∧ ‖b‖ ≤ ‖f‖ := by
  by_cases hf : f = 0
  · subst f
    exact ⟨0, 0, by simp, by simp, by simp⟩
  have hn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
  let c : ℂ := (‖f‖ : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hcn : ‖c‖ = ‖f‖ := by simp [c]
  obtain ⟨a, b, hab, ha, hb⟩ := lp_unit_decomposition μ p₀ p₁ p hpt h₀ h₁
    (c⁻¹ • f) (by simp [norm_smul, hcn, inv_mul_cancel₀ hn])
  refine ⟨c • a, c • b, ?_, ?_, ?_⟩
  · change c • (a : X →ₘ[μ] ℂ) + c • (b : X →ₘ[μ] ℂ) = _
    rw [← smul_add, hab]
    change c • (c⁻¹ • (f : X →ₘ[μ] ℂ)) = _
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  · simpa [norm_smul, hcn] using mul_le_mul_of_nonneg_left ha (norm_nonneg f)
  · simpa [norm_smul, hcn] using mul_le_mul_of_nonneg_left hb (norm_nonneg f)

open Filter in
/-- Addition preserves convergence in measure to zero, for arbitrary measures. -/
theorem tendstoInMeasure_add_zero {X : Type u} {ι : Type*} [MeasurableSpace X]
    (μ : Measure X) {l : Filter ι} {a b : ι → X → ℂ}
    (ha : TendstoInMeasure μ a l 0) (hb : TendstoInMeasure μ b l 0) :
    TendstoInMeasure μ (fun n x => a n x + b n x) l 0 := by
  rw [tendstoInMeasure_iff_norm] at ha hb ⊢
  intro ε hε
  have h := (ha (ε / 2) (by positivity)).add (hb (ε / 2) (by positivity))
  simp only [Pi.zero_apply, sub_zero, zero_add] at h ⊢
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro n
  apply le_trans (measure_mono ?_) (measure_union_le _ _)
  intro x hx
  by_contra hx'
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hx'
  have hn := norm_add_le (a n x) (b n x)
  simp only [Set.mem_ofPred_eq] at hx
  linarith [hx'.1, hx'.2]

open Filter in
/-- An endpoint bound sends endpoint norm convergence to convergence in measure. -/
theorem endpoint_tendstoInMeasure_zero {X : Type u} {Y : Type v} {ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {p₀ p₁ r s : ℝ≥0∞} {M : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (hT : EndpointBound T r s M) (hs : s ≠ 0)
    {l : Filter ι} (f : ι → SumSpace μ p₀ p₁)
    (hf : ∀ n, MemLp (f n : X →ₘ[μ] ℂ) r μ)
    (hconv : Tendsto (fun n => eLpNorm (f n : X →ₘ[μ] ℂ) r μ) l (𝓝 0)) :
    TendstoInMeasure ν (fun n => T (f n)) l 0 := by
  apply tendstoInMeasure_of_tendsto_eLpNorm hs
  simp only [sub_zero]
  have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M) hconv (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ => bot_le) (fun n => (hT (f n) (hf n)).2)

/-- The quantitative decomposition also holds when the endpoint order is reversed. -/
theorem lp_interpolation_decomposition {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : Interpolates p₀ p₁ p θ) (hpt : p ≠ ∞) (f : Lp ℂ p μ) :
    ∃ a : Lp ℂ p₀ μ, ∃ b : Lp ℂ p₁ μ,
      (a : X →ₘ[μ] ℂ) + (b : X →ₘ[μ] ℂ) = (f : X →ₘ[μ] ℂ) ∧
        ‖a‖ ≤ ‖f‖ ∧ ‖b‖ ≤ ‖f‖ := by
  rcases le_total p₀ p₁ with horder | horder
  · obtain ⟨h₀, h₁⟩ := interpolates_between _ _ _ θ hθ₀ hθ₁ hp horder
    exact lp_norm_decomposition μ p₀ p₁ p hpt h₀ h₁ f
  · have hswap : Interpolates p₁ p₀ p (1 - θ) := by
      have heq : 1 - (1 - θ) = θ := by ring
      simp only [Interpolates, heq, add_comm] at hp ⊢
      exact hp
    obtain ⟨h₀, h₁⟩ := interpolates_between _ _ _ (1 - θ)
      (sub_pos.mpr hθ₁) (by linarith) hswap horder
    obtain ⟨a, b, hab, ha, hb⟩ := lp_norm_decomposition μ p₁ p₀ p hpt h₀ h₁ f
    exact ⟨b, a, by simpa only [add_comm] using hab, hb, ha⟩

/-- The canonical inclusion into the common domain uses the same a.e. class. -/
def lpSumInclusion {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    (hinc : ∀ f : Lp ℂ p μ, (f : X →ₘ[μ] ℂ) ∈ SumSpace μ p₀ p₁) :
    Lp ℂ p μ →ₗ[ℂ] SumSpace μ p₀ p₁ where
  toFun f := ⟨f, hinc f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open Filter in
/-- Endpoint bounds force continuity in measure of the original operator on
an intermediate finite-p space. The operator is not replaced by an extension. -/
theorem sum_operator_tendstoInMeasure_zero
    {X : Type u} {Y : Type v} {ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (p₀ p₁ q₀ q₁ p : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ p)] (θ M₀ M₁ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : Interpolates p₀ p₁ p θ) (hpt : p ≠ ∞)
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    {l : Filter ι} (f : ι → Lp ℂ p μ)
    (hconv : Tendsto (fun n => eLpNorm (f n) p μ) l (𝓝 0))
    (hinc : ∀ g : Lp ℂ p μ, (g : X →ₘ[μ] ℂ) ∈ SumSpace μ p₀ p₁) :
    TendstoInMeasure ν (fun n => T (lpSumInclusion μ p₀ p₁ p hinc (f n))) l 0 := by
  choose a b hab ha hb using
    fun n => lp_interpolation_decomposition μ p₀ p₁ p θ hθ₀ hθ₁ hp hpt (f n)
  let A : ι → SumSpace μ p₀ p₁ := fun n =>
    ⟨a n, Submodule.mem_sup_left (a n).property⟩
  let B : ι → SumSpace μ p₀ p₁ := fun n =>
    ⟨b n, Submodule.mem_sup_right (b n).property⟩
  have hA : Tendsto (fun n => eLpNorm (A n : X →ₘ[μ] ℂ) p₀ μ) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ => bot_le)
    intro n
    change eLpNorm (a n) p₀ μ ≤ eLpNorm (f n) p μ
    simpa only [← Lp.enorm_def, enorm_le_iff_norm_le] using ha n
  have hB : Tendsto (fun n => eLpNorm (B n : X →ₘ[μ] ℂ) p₁ μ) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ => bot_le)
    intro n
    change eLpNorm (b n) p₁ μ ≤ eLpNorm (f n) p μ
    simpa only [← Lp.enorm_def, enorm_le_iff_norm_le] using hb n
  have hTA := endpoint_tendstoInMeasure_zero T h₀
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne' A (fun n => Lp.memLp (a n)) hA
  have hTB := endpoint_tendstoInMeasure_zero T h₁
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' B (fun n => Lp.memLp (b n)) hB
  apply (tendstoInMeasure_add_zero ν hTA hTB).congr_left
  intro n
  have heq : lpSumInclusion μ p₀ p₁ p hinc (f n) = A n + B n :=
    Subtype.ext (hab n).symm
  rw [heq, T.map_add]
  exact (AEEqFun.coeFn_add _ _).symm

open Filter in
/-- Fatou's inequality in measure, allowing a convergent sequence of bounds.
This includes q=1 and q=infinity. -/
theorem eLpNorm_le_of_tendstoInMeasure_varying_bound
    {Y : Type v} [MeasurableSpace Y] (ν : Measure Y)
    {g : ℕ → Y → ℂ} {g₀ : Y → ℂ} {q : ℝ≥0∞}
    {B : ℕ → ℝ≥0∞} {C : ℝ≥0∞}
    (hg : ∀ n, AEStronglyMeasurable (g n) ν)
    (hconv : TendstoInMeasure ν g atTop g₀)
    (hbound : ∀ n, eLpNorm (g n) q ν ≤ B n)
    (hB : Tendsto B atTop (𝓝 C)) : eLpNorm g₀ q ν ≤ C := by
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  calc
    eLpNorm g₀ q ν ≤ atTop.liminf (fun n => eLpNorm (g (ns n)) q ν) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hg (ns n)) g₀
        (hconv.aestronglyMeasurable hg) hae
    _ ≤ atTop.liminf (fun n => B (ns n)) :=
      liminf_le_liminf (Eventually.of_forall fun n => hbound (ns n))
    _ = C := (hB.comp hns.tendsto_atTop).liminf_eq

/-- A simple-input estimate extends to every finite-p input while preserving
exactly the original common-domain operator. -/
theorem riesz_thorin_density_transfer : DensityTransfer.{u,v} := by
  intro X Y _ _ μ ν p₀ p₁ q₀ q₁ p q _ _ _ _ _ θ M₀ M₁ C hθ₀ hθ₁ hp hpt T h₀ h₁ hsimple f
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hinc := lp_mem_interpolation_sum μ p₀ p₁ p θ hθ₀ hθ₁ hpz hp
  let S := lpSumInclusion μ p₀ p₁ p hinc
  let F := T.comp S
  obtain ⟨s, hs, hsf⟩ := mem_closure_iff_seq_limit.mp
    ((Lp.simpleFunc.dense (E := ℂ) (μ := μ) hpt) f)
  have hsnorm : Filter.Tendsto (fun n => eLpNorm (s n) p μ) Filter.atTop
      (𝓝 (eLpNorm f p μ)) := by
    simpa only [ofReal_norm, Lp.enorm_def] using ENNReal.tendsto_ofReal hsf.norm
  have herr : Filter.Tendsto (fun n => eLpNorm (s n - f) p μ) Filter.atTop (𝓝 0) := by
    have hc : Filter.Tendsto (fun n => s n - f) Filter.atTop (𝓝 0) := by
      simpa only [sub_self] using hsf.sub (tendsto_const_nhds (x := f))
    simpa only [norm_zero, ENNReal.ofReal_zero, ofReal_norm, Lp.enorm_def] using
      ENNReal.tendsto_ofReal hc.norm
  have hzero := sum_operator_tendstoInMeasure_zero μ ν p₀ p₁ q₀ q₁ p θ M₀ M₁
    hθ₀ hθ₁ hp hpt T h₀ h₁ (fun n => s n - f) herr hinc
  have hdiff : TendstoInMeasure ν (fun n y => F (s n) y - F f y) Filter.atTop 0 := by
    apply hzero.congr_left
    intro n
    change (F (s n - f) : Y → ℂ) =ᵐ[ν] _
    rw [F.map_sub]
    exact AEEqFun.coeFn_sub _ _
  have hout : TendstoInMeasure ν (fun n => F (s n)) Filter.atTop (F f) := by
    rw [tendstoInMeasure_iff_norm] at hdiff ⊢
    simpa only [Pi.zero_apply, sub_zero] using hdiff
  have hbound (n : ℕ) : eLpNorm (F (s n)) q ν ≤ ENNReal.ofReal C * eLpNorm (s n) p μ := by
    obtain ⟨g, hg⟩ := hs n
    have hgae : (g : X → ℂ) =ᵐ[μ] (s n : X → ℂ) := by
      rw [← hg]
      exact (AEEqFun.coeFn_mk _ _).symm
    have hgmem : MemLp g p μ := (Lp.memLp (s n)).ae_eq hgae.symm
    have hgfin : g.FinMeasSupp μ :=
      (SimpleFunc.memLp_iff_finMeasSupp hpz hpt).mp hgmem
    have hgsum : AEEqFun.mk g g.aestronglyMeasurable ∈ SumSpace μ p₀ p₁ := by
      rw [hg]
      exact hinc (s n)
    have hsame : (⟨AEEqFun.mk g g.aestronglyMeasurable, hgsum⟩ : SumSpace μ p₀ p₁) =
        S (s n) := Subtype.ext hg
    change eLpNorm (T (S (s n))) q ν ≤ _
    simpa only [hsame, eLpNorm_congr_ae hgae] using hsimple g hgfin hgsum
  have hB := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hsnorm
    (Or.inr ENNReal.ofReal_ne_top)
  have hfinal := eLpNorm_le_of_tendstoInMeasure_varying_bound ν
    (fun n => (F (s n)).aestronglyMeasurable) hout hbound hB
  refine ⟨hinc f, ?_, hfinal⟩
  exact hfinal.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f))

/-- Finite exponential sums with real slopes are bounded on the closed strip,
so three lines applies directly. This is the scalar analytic core used for
finite simple input and test families; no continuity of the original operator
outside their finite spans is needed. -/
theorem three_lines_finite_exponential_sum {ι : Type*}
    (s : Finset ι) (c b : ι → ℂ) (a : ι → ℝ) (M₀ M₁ θ : ℝ)
    (hleft : ∀ t : ℝ,
      ‖∑ i ∈ s, c i * Complex.exp ((a i : ℂ) * ((t : ℂ) * Complex.I) + b i)‖ ≤ M₀)
    (hright : ∀ t : ℝ,
      ‖∑ i ∈ s, c i * Complex.exp ((a i : ℂ) * (1 + (t : ℂ) * Complex.I) + b i)‖ ≤ M₁)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ‖∑ i ∈ s, c i * Complex.exp ((a i : ℂ) * (θ : ℂ) + b i)‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  let F : ℂ → ℂ := fun z => ∑ i ∈ s, c i * Complex.exp ((a i : ℂ) * z + b i)
  have hd : Differentiable ℂ F := by
    dsimp [F]
    fun_prop
  have hbdd : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ C := by
    refine ⟨∑ i ∈ s, ‖c i‖ * Real.exp (|a i| + (b i).re), ?_⟩
    intro z hz₀ hz₁
    apply le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact add_le_add
      ((mul_le_mul_of_nonneg_right (le_abs_self (a i)) hz₀).trans
        (mul_le_of_le_one_right (abs_nonneg _) hz₁)) le_rfl
  exact three_lines F M₀ M₁ θ hbdd hd.continuous.continuousOn hd.differentiableOn
    hleft hright hθ₀ hθ₁

/-- The full theorem reduces only to the sharp finite-simple-input estimate.
This implication records completed assembly, not a proof of its premise. -/
theorem riesz_thorin_of_simple_estimate (hsharp : SimpleEstimate.{u,v}) :
    RieszThorin.{u,v} := by
  intro X Y _ _ μ ν _ _ p₀ p₁ q₀ q₁ p q _ _ _ _ _ _ θ M₀ M₁
    hθ₀ hθ₁ hM₀ hM₁ hp hq T h₀ h₁ f
  by_cases hpt : p = ∞
  · subst p
    obtain ⟨rfl, rfl⟩ := (interpolates_top_iff _ _ _ hθ₀ hθ₁).mp hp
    exact riesz_thorin_infinity_domain μ ν q₀ q₁ q θ M₀ M₁
      hθ₀ hθ₁ hM₀ hM₁ hq T h₀ h₁ f
  obtain ⟨hf, hmem, hbound⟩ := riesz_thorin_density_transfer μ ν p₀ p₁ q₀ q₁ p q
    θ M₀ M₁ (M₀ ^ (1 - θ) * M₁ ^ θ) hθ₀ hθ₁ hp hpt T h₀ h₁
    (hsharp μ ν p₀ p₁ q₀ q₁ p q θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hp hq hpt T h₀ h₁) f
  have hfinite : ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)
  refine ⟨hf, hmem, ?_⟩
  have hreal := ENNReal.toReal_mono hfinite.ne hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ), ← Lp.norm_def] using hreal



theorem interpolates_conjugates
    (q₀ q₁ q r₀ r₁ r : ℝ≥0∞) (θ : ℝ)
    [ENNReal.HolderConjugate q₀ r₀] [ENNReal.HolderConjugate q₁ r₁]
    [ENNReal.HolderConjugate q r]
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hq : Interpolates q₀ q₁ q θ) : Interpolates r₀ r₁ r θ := by
  have hab : ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hθ₁) hθ₀]
    simp
  have hh : ENNReal.HolderConjugate q
      (ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹)⁻¹ := by
    apply ENNReal.holderConjugate_iff.mpr
    rw [inv_inv, hq]
    calc
      _ = ENNReal.ofReal (1 - θ) * (q₀⁻¹ + r₀⁻¹) +
          ENNReal.ofReal θ * (q₁⁻¹ + r₁⁻¹) := by ring
      _ = 1 := by
        rw [ENNReal.HolderConjugate.inv_add_inv_eq_one q₀ r₀,
          ENNReal.HolderConjugate.inv_add_inv_eq_one q₁ r₁, mul_one, mul_one, hab]
  have heq := @ENNReal.HolderConjugate.unique q r _
    (ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹)⁻¹ hh
  exact congrArg Inv.inv heq |>.trans (inv_inv _)

theorem interpolates_one_iff (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    Interpolates q₀ q₁ 1 θ ↔ q₀ = 1 ∧ q₁ = 1 := by
  constructor
  · intro hq
    have hr : Interpolates (ENNReal.conjExponent q₀) (ENNReal.conjExponent q₁) ∞ θ :=
      interpolates_conjugates q₀ q₁ 1 (ENNReal.conjExponent q₀)
        (ENNReal.conjExponent q₁) ∞ θ hθ₀.le hθ₁.le hq
    obtain ⟨h₀, h₁⟩ := (interpolates_top_iff _ _ _ hθ₀ hθ₁).mp hr
    exact ⟨(ENNReal.HolderConjugate.eq_top_iff_eq_one _ _).mp h₀,
      (ENNReal.HolderConjugate.eq_top_iff_eq_one _ _).mp h₁⟩
  · rintro ⟨rfl, rfl⟩
    simp only [Interpolates, inv_one, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hθ₁.le) hθ₀.le]
    simp

theorem interpolates_inverse_toReal (p₀ p₁ p : ℝ≥0∞) (θ : ℝ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0)
    (hp : Interpolates p₀ p₁ p θ) :
    (p⁻¹).toReal = (1 - θ) * (p₀⁻¹).toReal + θ * (p₁⁻¹).toReal := by
  rw [hp, ENNReal.toReal_add]
  · simp only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hθ₁), ENNReal.toReal_ofReal hθ₀]
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simpa using hp₀)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simpa using hp₁)

theorem interpolates_center_real (p₀ p₁ p : ℝ≥0∞) (θ : ℝ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0)
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hp : Interpolates p₀ p₁ p θ) :
    p.toReal * ((1 - θ) * (p₀⁻¹).toReal + θ * (p₁⁻¹).toReal) = 1 := by
  rw [← interpolates_inverse_toReal p₀ p₁ p θ hθ₀ hθ₁ hp₀ hp₁ hp,
    ENNReal.toReal_inv]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hpz, hpt⟩)


namespace SimpleInterpolation

def powerCoeff (c w : ℂ) : ℂ := c * Complex.exp ((Real.log ‖c‖ : ℂ) * (w - 1))
@[simp] lemma powerCoeff_zero (w : ℂ) : powerCoeff 0 w = 0 := by simp [powerCoeff]
@[simp] lemma powerCoeff_one (c : ℂ) : powerCoeff c 1 = c := by simp [powerCoeff]

lemma norm_powerCoeff_of_ne_zero {c w : ℂ} (hc : c ≠ 0) :
    ‖powerCoeff c w‖ = ‖c‖ ^ w.re := by
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [powerCoeff, norm_mul, Complex.norm_exp, Real.rpow_def_of_pos hn]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.one_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [mul_sub, mul_one, Real.exp_sub, Real.exp_log hn]
  field_simp

lemma norm_powerCoeff_of_pos {c w : ℂ} (hw : 0 < w.re) :
    ‖powerCoeff c w‖ = ‖c‖ ^ w.re := by
  by_cases hc : c = 0
  · simp [hc, Real.zero_rpow hw.ne']
  · exact norm_powerCoeff_of_ne_zero hc

lemma norm_powerCoeff_zero_re {c w : ℂ} (hw : w.re = 0) :
    ‖powerCoeff c w‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [norm_powerCoeff_of_ne_zero hc, hw, Real.rpow_zero]

def powerFamily {X : Type*} [MeasurableSpace X] (s : SimpleFunc X ℂ) (w : ℂ) :
    SimpleFunc X ℂ := s.map (fun c => powerCoeff c w)
@[simp] lemma powerFamily_apply {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (w : ℂ) (x : X) : powerFamily s w x = powerCoeff (s x) w := rfl
@[simp] lemma powerFamily_one {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) : powerFamily s 1 = s := by ext x; simp
lemma powerFamily_finMeasSupp {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (μ : Measure X) (hs : s.FinMeasSupp μ) (w : ℂ) :
    (powerFamily s w).FinMeasSupp μ := hs.map (powerCoeff_zero w)

lemma powerFamily_memLp {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (μ : Measure X) (hs : s.FinMeasSupp μ) (w : ℂ) (r : ℝ≥0∞) :
    MemLp (powerFamily s w) r μ := by
  by_cases hr₀ : r = 0
  · simpa [hr₀] using (powerFamily s w).memLp_zero μ
  by_cases hrt : r = ∞
  · simpa [hrt] using (powerFamily s w).memLp_top μ
  exact (SimpleFunc.memLp_iff_finMeasSupp hr₀ hrt).mpr (powerFamily_finMeasSupp s μ hs w)

lemma eLpNorm_powerFamily_top_le_one {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (μ : Measure X) (w : ℂ) (hw : w.re = 0) :
    eLpNorm (powerFamily s w) ∞ μ ≤ 1 := by
  rw [eLpNorm_exponent_top (powerFamily s w).aestronglyMeasurable]
  simpa only [ENNReal.ofReal_one] using eLpNormEssSup_le_of_ae_bound (show ∀ᵐ x ∂μ, ‖powerFamily s w x‖ ≤ (1 : ℝ) from by
    filter_upwards with x
    exact norm_powerCoeff_zero_re hw)

lemma eLpNorm_powerFamily {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (μ : Measure X) (r : ℝ≥0∞) (w : ℂ) (hw : 0 < w.re) :
    eLpNorm (powerFamily s w) r μ =
      eLpNorm s (r * ENNReal.ofReal w.re) μ ^ w.re := by
  calc
    _ = eLpNorm (fun x => ‖s x‖ ^ w.re) r μ := by
      apply eLpNorm_congr_norm_ae (powerFamily s w).aestronglyMeasurable (by fun_prop)
      filter_upwards with x
      simp only [powerFamily_apply, norm_powerCoeff_of_pos hw,
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    _ = _ := eLpNorm_norm_rpow s s.aestronglyMeasurable hw

def interpolationParam (P a b : ℝ) (z : ℂ) : ℂ :=
  (P : ℂ) * ((1 - z) * (a : ℂ) + z * (b : ℂ))
lemma interpolationParam_re (P a b : ℝ) (z : ℂ) :
    (interpolationParam P a b z).re = P * ((1 - z.re) * a + z.re * b) := by
  simp [interpolationParam, Complex.mul_re]
lemma interpolationParam_left (P a b t : ℝ) :
    (interpolationParam P a b ((t : ℂ) * Complex.I)).re = P * a := by
  simp [interpolationParam_re]
lemma interpolationParam_right (P a b t : ℝ) :
    (interpolationParam P a b (1 + (t : ℂ) * Complex.I)).re = P * b := by
  simp [interpolationParam_re]
lemma interpolationParam_center (P a b θ : ℝ) (hP : P ≠ 0)
    (h : (1 - θ) * a + θ * b = P⁻¹) :
    interpolationParam P a b (θ : ℂ) = 1 := by
  have hcomplex : ((1 : ℂ) - θ) * (a : ℂ) + θ * (b : ℂ) = ((P⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast h
  rw [interpolationParam, hcomplex]
  exact_mod_cast (mul_inv_cancel₀ hP)

lemma endpoint_scale {p r : ℝ≥0∞} (hp : p ≠ ∞) (hr₀ : r ≠ 0) (hrt : r ≠ ∞) :
    r * ENNReal.ofReal (p.toReal * (r⁻¹).toReal) = p := by
  rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal]
  · calc
      r * (p * r⁻¹) = p * (r * r⁻¹) := by ring
      _ = p := by rw [ENNReal.mul_inv_cancel hr₀ hrt, mul_one]
  · exact ENNReal.mul_ne_top hp (ENNReal.inv_ne_top.mpr hr₀)

lemma eLpNorm_powerFamily_endpoint {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (μ : Measure X) (p r : ℝ≥0∞)
    (hp₀ : p ≠ 0) (hpt : p ≠ ∞) (hr₀ : r ≠ 0) (hrt : r ≠ ∞)
    (w : ℂ) (hw : w.re = p.toReal * (r⁻¹).toReal) :
    eLpNorm (powerFamily s w) r μ = eLpNorm s p μ ^ (p.toReal * (r⁻¹).toReal) := by
  have hpos : 0 < w.re := by
    rw [hw]
    exact mul_pos (ENNReal.toReal_pos hp₀ hpt)
      (ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hrt) (ENNReal.inv_ne_top.mpr hr₀))
  rw [eLpNorm_powerFamily s μ r w hpos, hw, endpoint_scale hpt hr₀ hrt]

lemma eLpNorm_powerFamily_endpoint_le_one {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (μ : Measure X) (p r : ℝ≥0∞)
    (hp₀ : p ≠ 0) (hpt : p ≠ ∞) (hr₀ : r ≠ 0)
    (hs : eLpNorm s p μ ≤ 1) (w : ℂ)
    (hw : w.re = p.toReal * (r⁻¹).toReal) :
    eLpNorm (powerFamily s w) r μ ≤ 1 := by
  by_cases hrt : r = ∞
  · subst r
    apply eLpNorm_powerFamily_top_le_one s μ w
    simpa using hw
  · rw [eLpNorm_powerFamily_endpoint s μ p r hp₀ hpt hr₀ hrt w hw]
    exact (ENNReal.rpow_le_rpow hs (by positivity)).trans_eq (by simp)

def powerAtom {X : Type*} [MeasurableSpace X] (s : SimpleFunc X ℂ) (c : ℂ) :
    SimpleFunc X ℂ := s.restrict (s ⁻¹' {c})
lemma powerAtom_apply {X : Type*} [MeasurableSpace X] (s : SimpleFunc X ℂ) (c : ℂ) (x : X) :
    powerAtom s c x = if s x = c then s x else 0 := by
  rw [powerAtom, SimpleFunc.restrict_apply _ (s.measurableSet_fiber c)]
  rfl
lemma powerAtom_finMeasSupp {X : Type*} [MeasurableSpace X] (s : SimpleFunc X ℂ)
    (μ : Measure X) (hs : s.FinMeasSupp μ) (c : ℂ) : (powerAtom s c).FinMeasSupp μ := by
  change μ (Function.support (powerAtom s c)) < ∞
  change μ (Function.support s) < ∞ at hs
  apply lt_of_le_of_lt (measure_mono ?_) hs
  intro x hx
  change s x ≠ 0
  intro h
  exact hx (by simp [powerAtom_apply, h])

lemma powerCoeff_affine (c : ℂ) (P a b : ℝ) (z : ℂ) :
    powerCoeff c (interpolationParam P a b z) =
      Complex.exp (((Real.log ‖c‖ * P * (b - a) : ℝ) : ℂ) * z +
        ((Real.log ‖c‖ * (P * a - 1) : ℝ) : ℂ)) * c := by
  unfold powerCoeff interpolationParam
  have hexp : (Real.log ‖c‖ : ℂ) *
      ((P : ℂ) * ((1 - z) * (a : ℂ) + z * (b : ℂ)) - 1) =
      (((Real.log ‖c‖ * P * (b - a) : ℝ) : ℂ) * z +
        ((Real.log ‖c‖ * (P * a - 1) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hexp, mul_comm]

lemma simpleFunc_sum_apply {X ι : Type*} [MeasurableSpace X]
    (S : Finset ι) (f : ι → SimpleFunc X ℂ) (x : X) :
    (∑ i ∈ S, f i) x = ∑ i ∈ S, f i x := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert i S hi ih => simp [Finset.sum_insert hi, SimpleFunc.add_apply, ih]

lemma powerFamily_eq_sum {X : Type*} [MeasurableSpace X]
    (s : SimpleFunc X ℂ) (P a b : ℝ) (z : ℂ) :
    powerFamily s (interpolationParam P a b z) =
      ∑ c ∈ s.range,
        Complex.exp (((Real.log ‖c‖ * P * (b - a) : ℝ) : ℂ) * z +
          ((Real.log ‖c‖ * (P * a - 1) : ℝ) : ℂ)) • powerAtom s c := by
  classical
  ext x
  simp only [powerFamily_apply, simpleFunc_sum_apply, SimpleFunc.smul_apply,
    smul_eq_mul, powerAtom_apply]
  rw [Finset.sum_eq_single (s x)]
  · simp only [ite_true]
    exact powerCoeff_affine (s x) P a b z
  · intro c hc hcx
    simp [Ne.symm hcx]
  · intro hx
    exact False.elim (hx (SimpleFunc.mem_range_self s x))

end SimpleInterpolation

 theorem bilinear_exponential_sum_eq
    {E F : Type*} [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (x : ι → E) (y : κ → F)
    (a : ι → ℝ) (b : ι → ℂ) (d : κ → ℝ) (e : κ → ℂ) (z : ℂ) :
    B (∑ i ∈ s, Complex.exp ((a i : ℂ) * z + b i) • x i)
      (∑ j ∈ t, Complex.exp ((d j : ℂ) * z + e j) • y j) =
      ∑ ij ∈ s ×ˢ t, (B (x ij.1) (y ij.2)) *
        Complex.exp (((a ij.1 + d ij.2 : ℝ) : ℂ) * z + (b ij.1 + e ij.2)) := by
  rw [map_sum B, LinearMap.sum_apply, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  rw [show (((a i + d j : ℝ) : ℂ) * z + (b i + e j)) =
    ((a i : ℂ) * z + b i) + ((d j : ℂ) * z + e j) by push_cast; ring]
  simp only [Complex.exp_add]
  ring

 theorem three_lines_bilinear_exponential_sum
    {E F : Type*} [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (x : ι → E) (y : κ → F)
    (a : ι → ℝ) (b : ι → ℂ) (d : κ → ℝ) (e : κ → ℂ) (M₀ M₁ θ : ℝ)
    (hleft : ∀ r : ℝ,
      ‖B (∑ i ∈ s, Complex.exp ((a i : ℂ) * ((r : ℂ) * Complex.I) + b i) • x i)
        (∑ j ∈ t, Complex.exp ((d j : ℂ) * ((r : ℂ) * Complex.I) + e j) • y j)‖ ≤ M₀)
    (hright : ∀ r : ℝ,
      ‖B (∑ i ∈ s, Complex.exp ((a i : ℂ) * (1 + (r : ℂ) * Complex.I) + b i) • x i)
        (∑ j ∈ t, Complex.exp ((d j : ℂ) * (1 + (r : ℂ) * Complex.I) + e j) • y j)‖ ≤ M₁)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ‖B (∑ i ∈ s, Complex.exp ((a i : ℂ) * (θ : ℂ) + b i) • x i)
        (∑ j ∈ t, Complex.exp ((d j : ℂ) * (θ : ℂ) + e j) • y j)‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  simp_rw [bilinear_exponential_sum_eq] at hleft hright ⊢
  exact three_lines_finite_exponential_sum (s ×ˢ t)
    (fun ij => B (x ij.1) (y ij.2)) (fun ij => b ij.1 + e ij.2)
    (fun ij => a ij.1 + d ij.2) M₀ M₁ θ hleft hright hθ₀ hθ₁



/-- Simple scalar functions with support of finite measure form a complex vector space. -/
def finiteSimpleSubmodule {Y : Type v} [MeasurableSpace Y] (ν : Measure Y) :
    Submodule ℂ (SimpleFunc Y ℂ) where
  carrier := {h | h.FinMeasSupp ν}
  zero_mem' := by
    change ν (Function.support (0 : SimpleFunc Y ℂ)) < ∞
    simp
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := by
    intro c f hf
    rw [SimpleFunc.smul_eq_map]
    exact hf.map (by simp)

/-- Finite support simple functions belong to all Lp classes, including infinity. -/
theorem finiteSimple_memLp {Y : Type v} [MeasurableSpace Y] (ν : Measure Y)
    (h : finiteSimpleSubmodule ν) (r : ℝ≥0∞) : MemLp h.val r ν :=
  SimpleFunc.memLp_of_finite_measure_preimage r
    (SimpleFunc.finMeasSupp_iff.mp (show h.val.FinMeasSupp ν from h.property))

theorem sum_output_mul_finiteSimple_integrable
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ q₀ q₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (f : SumSpace μ p₀ p₁) (h : finiteSimpleSubmodule ν) :
    Integrable (fun y => T f y * h.val y) ν := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp f.property
  let A : SumSpace μ p₀ p₁ := ⟨a, Submodule.mem_sup_left ha⟩
  let B : SumSpace μ p₀ p₁ := ⟨b, Submodule.mem_sup_right hb⟩
  have hA : MemLp (T A) q₀ ν := (h₀ A (Lp.mem_Lp_iff_memLp.mp ha)).1
  have hB : MemLp (T B) q₁ ν := (h₁ B (Lp.mem_Lp_iff_memLp.mp hb)).1
  have hAi := hA.integrable_mul (finiteSimple_memLp ν h (ENNReal.conjExponent q₀))
  have hBi := hB.integrable_mul (finiteSimple_memLp ν h (ENNReal.conjExponent q₁))
  have hAB : A + B = f := Subtype.ext hab
  apply (hAi.add hBi).congr
  rw [← hAB, map_add]
  filter_upwards [AEEqFun.coeFn_add (T A) (T B)] with y hy
  simp [hy, add_mul]

/-- The common-domain scalar integral pairing is bilinear on finite simple tests. -/
def sumFiniteSimplePairing
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ q₀ q₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁) :
    SumSpace μ p₀ p₁ →ₗ[ℂ] finiteSimpleSubmodule ν →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun h := ∫ y, T f y * h.val y ∂ν
      map_add' := by
        intro h k
        change (∫ y, T f y * (h.val + k.val) y ∂ν) = _
        simp only [SimpleFunc.coe_add, Pi.add_apply, mul_add]
        exact integral_add (sum_output_mul_finiteSimple_integrable T h₀ h₁ f h)
          (sum_output_mul_finiteSimple_integrable T h₀ h₁ f k)
      map_smul' := by
        intro c h
        change (∫ y, T f y * (c • h.val) y ∂ν) = c • _
        simp only [SimpleFunc.coe_smul, Pi.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (T f _) c]
        exact integral_const_mul c _ }
  map_add' := by
    intro f g
    ext h
    change (∫ y, T (f + g) y * h.val y ∂ν) =
      (∫ y, T f y * h.val y ∂ν) + (∫ y, T g y * h.val y ∂ν)
    rw [map_add, ← integral_add (sum_output_mul_finiteSimple_integrable T h₀ h₁ f h)
      (sum_output_mul_finiteSimple_integrable T h₀ h₁ g h)]
    apply integral_congr_ae
    filter_upwards [AEEqFun.coeFn_add (T f) (T g)] with y hy
    simp [hy, add_mul]
  map_smul' := by
    intro c f
    ext h
    change (∫ y, T (c • f) y * h.val y ∂ν) = c • (∫ y, T f y * h.val y ∂ν)
    rw [map_smul]
    simp only [smul_eq_mul]
    rw [← integral_const_mul c]
    apply integral_congr_ae
    filter_upwards [AEEqFun.coeFn_smul c (T f)] with y hy
    simp [hy, mul_assoc]

theorem enorm_integral_mul_le_eLpNorm_mul_eLpNorm
    {Y : Type v} [MeasurableSpace Y] (ν : Measure Y)
    (q r : ℝ≥0∞) [ENNReal.HolderConjugate q r]
    (g h : Y → ℂ) (hg : AEStronglyMeasurable g ν) (hh : AEStronglyMeasurable h ν) :
    ‖∫ y, g y * h y ∂ν‖ₑ ≤ eLpNorm g q ν * eLpNorm h r ν := by
  calc
    _ ≤ ∫⁻ y, ‖g y * h y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun y => g y * h y) 1 ν :=
      (eLpNorm_one_eq_lintegral_enorm (hg.mul hh)).symm
    _ ≤ _ := by
      simpa only [ENNReal.coe_one, one_mul] using
        (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := q) (q := r) (r := 1) (fun a b : ℂ => a * b) 1
          continuous_mul hg hh (by filter_upwards with y; simp))

theorem sumFiniteSimplePairing_endpoint_le
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ q₀ q₁ p q r : ℝ≥0∞} {M₀ M₁ M : ℝ}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [ENNReal.HolderConjugate q r]
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (hT : EndpointBound T p q M) (hM : 0 ≤ M)
    (f : SumSpace μ p₀ p₁) (hf : MemLp (f : X →ₘ[μ] ℂ) p μ)
    (h : finiteSimpleSubmodule ν)
    (hfn : eLpNorm (f : X →ₘ[μ] ℂ) p μ ≤ 1) (hhn : eLpNorm h.val r ν ≤ 1) :
    ‖sumFiniteSimplePairing T h₀ h₁ f h‖ ≤ M := by
  have he : ‖sumFiniteSimplePairing T h₀ h₁ f h‖ₑ ≤ ENNReal.ofReal M := by
    calc
      _ ≤ eLpNorm (T f) q ν * eLpNorm h.val r ν :=
        enorm_integral_mul_le_eLpNorm_mul_eLpNorm ν q r (T f) h.val
          (T f).aestronglyMeasurable h.val.aestronglyMeasurable
      _ ≤ (ENNReal.ofReal M * eLpNorm (f : X →ₘ[μ] ℂ) p μ) * 1 :=
        mul_le_mul' (hT f hf).2 hhn
      _ ≤ _ := by simpa using mul_le_mul' (le_refl (ENNReal.ofReal M)) hfn
  simpa only [toReal_enorm, ENNReal.toReal_ofReal hM] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top he


/-- Natural linear map to the common a.e. quotient sum domain. -/
def finiteSimpleToSum {X : Type*} [MeasurableSpace X] (μ : Measure X) (p₀ p₁ : ℝ≥0∞) :
    finiteSimpleSubmodule μ →ₗ[ℂ] SumSpace μ p₀ p₁ where
  toFun s := ⟨AEEqFun.mk s.val s.val.aestronglyMeasurable,
    Submodule.mem_sup_left (Lp.mem_Lp_iff_memLp.mpr
      ((finiteSimple_memLp μ s p₀).ae_eq (AEEqFun.coeFn_mk _ _).symm))⟩
  map_add' := by
    intro s t
    apply Subtype.ext
    change AEEqFun.mk (s.val + t.val) _ = _
    exact (AEEqFun.mk_add_mk _ _ _ _).symm
  map_smul' := by
    intro c s
    apply Subtype.ext
    change AEEqFun.mk (c • s.val) _ = _
    exact (AEEqFun.smul_mk c _ _).symm

@[simp] theorem finiteSimpleToSum_coe {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ : ℝ≥0∞) (s : finiteSimpleSubmodule μ) :
    ((finiteSimpleToSum μ p₀ p₁ s : SumSpace μ p₀ p₁) : X →ₘ[μ] ℂ) =
      AEEqFun.mk s.val s.val.aestronglyMeasurable := rfl

namespace SimpleInterpolation

def finitePowerFamily {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : finiteSimpleSubmodule μ) (w : ℂ) : finiteSimpleSubmodule μ :=
  ⟨powerFamily s.val w, powerFamily_finMeasSupp s.val μ s.property w⟩

def finitePowerAtom {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : finiteSimpleSubmodule μ) (c : ℂ) : finiteSimpleSubmodule μ :=
  ⟨powerAtom s.val c, powerAtom_finMeasSupp s.val μ s.property c⟩

lemma finitePowerFamily_eq_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : finiteSimpleSubmodule μ) (P a b : ℝ) (z : ℂ) :
    finitePowerFamily μ s (interpolationParam P a b z) =
      ∑ c ∈ s.val.range,
        Complex.exp (((Real.log ‖c‖ * P * (b - a) : ℝ) : ℂ) * z +
          ((Real.log ‖c‖ * (P * a - 1) : ℝ) : ℂ)) • finitePowerAtom μ s c := by
  apply Subtype.ext
  change powerFamily s.val (interpolationParam P a b z) = _
  rw [powerFamily_eq_sum]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rfl

lemma finitePowerFamily_sum_domain {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ : ℝ≥0∞) (s : finiteSimpleSubmodule μ)
    (P a b : ℝ) (z : ℂ) :
    finiteSimpleToSum μ p₀ p₁ (finitePowerFamily μ s (interpolationParam P a b z)) =
      ∑ c ∈ s.val.range,
        Complex.exp (((Real.log ‖c‖ * P * (b - a) : ℝ) : ℂ) * z +
          ((Real.log ‖c‖ * (P * a - 1) : ℝ) : ℂ)) •
            finiteSimpleToSum μ p₀ p₁ (finitePowerAtom μ s c) := by
  rw [finitePowerFamily_eq_sum, map_sum]
  simp only [map_smul]

end SimpleInterpolation

namespace NormDetection

variable {X : Type u} [MeasurableSpace X]

theorem norm_le_of_simple_tests (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ∞)
    (g : Lp ℂ q μ) (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ s : SimpleFunc X ℂ, s.FinMeasSupp μ →
      ‖∫ x, s x * g x ∂μ‖ ≤ C * (eLpNorm s p μ).toReal) : ‖g‖ ≤ C := by
  let L := D11.Ch20.IntegralPairing.pairing μ p q g
  have hclosed : IsClosed {f : Lp ℂ p μ | ‖L f‖ ≤ C * ‖f‖} :=
    isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)
  have hnorm : ∀ f : Lp ℂ p μ, ‖L f‖ ≤ C * ‖f‖ := by
    intro f
    apply closure_minimal (t := {f : Lp ℂ p μ | ‖L f‖ ≤ C * ‖f‖}) ?_ hclosed
      ((Lp.simpleFunc.dense (E := ℂ) (μ := μ) hp) f)
    rintro f ⟨s, hs⟩
    have hae : (s : X → ℂ) =ᵐ[μ] (f : X → ℂ) := by
      rw [← hs]
      exact (AEEqFun.coeFn_mk _ _).symm
    have hmem : MemLp s p μ := (Lp.memLp f).ae_eq hae.symm
    have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    have hsfin : s.FinMeasSupp μ := (SimpleFunc.memLp_iff_finMeasSupp hpz hp).mp hmem
    change ‖Specs.D11.Ch20.IntegralPairing.pairing_value μ p q g f‖ ≤ C * ‖f‖
    rw [(D11.Ch20.IntegralPairing.pairing_eq_integral μ p q g f).2]
    have hi : (∫ x, s x * g x ∂μ) = ∫ x, f x * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    rw [← hi]
    simpa only [eLpNorm_congr_ae hae, ← Lp.norm_def] using htest s hsfin
  have hLn : ‖L‖ ≤ C := ContinuousLinearMap.opNorm_le_bound L hC hnorm
  exact (D11.Ch20.LpDualSigmafiniteLocal.pairing_norm μ p q g).symm.trans_le hLn

theorem norm_one_le_of_bounded_simple_tests (μ : Measure X)
    (g : Lp ℂ 1 μ) (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ s : SimpleFunc X ℂ,
      ‖∫ x, s x * g x ∂μ‖ ≤ C * (eLpNorm s ∞ μ).toReal) : ‖g‖ ≤ C := by
  let L := D11.Ch20.IntegralPairing.pairing μ ∞ 1 g
  have hdense : Dense (Lp.simpleFunc ℂ ∞ μ : Set (Lp ℂ ∞ μ)) := by
    intro f
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨s, hs, _, hdist⟩ :=
      D11.Ch11.BoundedSimpleInfinity.native_approximation μ f ε hε
    refine ⟨hs.toLp s, ?_, ?_⟩
    · exact ⟨s, rfl⟩
    · simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hclosed : IsClosed {f : Lp ℂ ∞ μ | ‖L f‖ ≤ C * ‖f‖} :=
    isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)
  have hnorm : ∀ f : Lp ℂ ∞ μ, ‖L f‖ ≤ C * ‖f‖ := by
    intro f
    apply closure_minimal (t := {f : Lp ℂ ∞ μ | ‖L f‖ ≤ C * ‖f‖}) ?_ hclosed (hdense f)
    rintro f ⟨s, hs⟩
    have hae : (s : X → ℂ) =ᵐ[μ] (f : X → ℂ) := by
      rw [← hs]
      exact (AEEqFun.coeFn_mk _ _).symm
    change ‖Specs.D11.Ch20.IntegralPairing.pairing_value μ ∞ 1 g f‖ ≤ C * ‖f‖
    rw [(D11.Ch20.IntegralPairing.pairing_eq_integral μ ∞ 1 g f).2]
    have hi : (∫ x, s x * g x ∂μ) = ∫ x, f x * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    rw [← hi]
    simpa only [eLpNorm_congr_ae hae, ← Lp.norm_def] using htest s
  have hLn : ‖L‖ ≤ C := ContinuousLinearMap.opNorm_le_bound L hC hnorm
  exact (D11.Ch20.PairingNormFiniteQ.norm_pairing_one μ g).symm.trans_le hLn


end NormDetection

theorem simpleInputBound_of_unit_bound
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ p q : ℝ≥0∞}
    (hpz : p ≠ 0) (hpt : p ≠ ∞)
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ)) (C : ℝ)
    (hunit : ∀ s : SimpleFunc X ℂ, s.FinMeasSupp μ →
      ∀ hs : AEEqFun.mk s s.aestronglyMeasurable ∈ SumSpace μ p₀ p₁,
        eLpNorm s p μ ≤ 1 →
        eLpNorm (T ⟨AEEqFun.mk s s.aestronglyMeasurable, hs⟩) q ν ≤ ENNReal.ofReal C) :
    SimpleInputBound T p q C := by
  intro s hs hsdom
  have hmem : MemLp s p μ := (SimpleFunc.memLp_iff_finMeasSupp hpz hpt).mpr hs
  by_cases hn : eLpNorm s p μ = 0
  · have hae : (s : X → ℂ) =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hpz).mp hn
    have hzero : (AEEqFun.mk s s.aestronglyMeasurable : X →ₘ[μ] ℂ) = 0 := by
      apply AEEqFun.ext
      exact (AEEqFun.coeFn_mk _ _).trans (hae.trans (AEEqFun.coeFn_zero).symm)
    have hvec : (⟨AEEqFun.mk s s.aestronglyMeasurable, hsdom⟩ : SumSpace μ p₀ p₁) = 0 :=
      Subtype.ext hzero
    rw [hvec, T.map_zero, hn, mul_zero]
    rw [eLpNorm_congr_ae (AEEqFun.coeFn_zero), eLpNorm_zero]
  let a : ℂ := ((eLpNorm s p μ).toReal : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hn, hmem.eLpNorm_ne_top⟩)
  have han : ‖a‖ₑ = eLpNorm s p μ := by
    rw [← ofReal_norm]
    simp only [a, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  let t : SimpleFunc X ℂ := a⁻¹ • s
  have ht : t.FinMeasSupp μ := by
    rw [show t = s.map (a⁻¹ • ·) from SimpleFunc.smul_eq_map _ _]
    exact hs.map (smul_zero _)
  have htv : (AEEqFun.mk t t.aestronglyMeasurable : X →ₘ[μ] ℂ) =
      a⁻¹ • AEEqFun.mk s s.aestronglyMeasurable := rfl
  have htdom : AEEqFun.mk t t.aestronglyMeasurable ∈ SumSpace μ p₀ p₁ := by
    rw [htv]
    exact Submodule.smul_mem _ _ hsdom
  have htnorm : eLpNorm t p μ ≤ 1 := by
    change eLpNorm (a⁻¹ • (s : X → ℂ)) p μ ≤ 1
    rw [eLpNorm_const_smul, enorm_inv ha, han,
      ENNReal.inv_mul_cancel hn hmem.eLpNorm_ne_top]
  have hvec : (⟨AEEqFun.mk s s.aestronglyMeasurable, hsdom⟩ : SumSpace μ p₀ p₁) =
      a • (⟨AEEqFun.mk t t.aestronglyMeasurable, htdom⟩ : SumSpace μ p₀ p₁) := by
    apply Subtype.ext
    change AEEqFun.mk s s.aestronglyMeasurable = a • AEEqFun.mk t t.aestronglyMeasurable
    rw [htv, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have hbound := hunit t ht htdom htnorm
  rw [hvec, T.map_smul]
  calc
    eLpNorm (a • T ⟨AEEqFun.mk t t.aestronglyMeasurable, htdom⟩) q ν
        = ‖a‖ₑ * eLpNorm (T ⟨AEEqFun.mk t t.aestronglyMeasurable, htdom⟩) q ν := by
          rw [eLpNorm_congr_ae (AEEqFun.coeFn_smul a _), eLpNorm_const_smul]
    _ ≤ ‖a‖ₑ * ENNReal.ofReal C := mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal C * eLpNorm s p μ := by rw [han, mul_comm]



theorem finiteSimple_output_memLp
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {M₀ M₁ θ : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hq : Interpolates q₀ q₁ q θ)
    (s : finiteSimpleSubmodule μ) :
    MemLp (T (finiteSimpleToSum μ p₀ p₁ s)) q ν := by
  let f := finiteSimpleToSum μ p₀ p₁ s
  have hf (r : ℝ≥0∞) : MemLp (f : X →ₘ[μ] ℂ) r μ :=
    (finiteSimple_memLp μ s r).ae_eq (AEEqFun.coeFn_mk _ _).symm
  have h₀f := (h₀ f (hf p₀)).1
  have h₁f := (h₁ f (hf p₁)).1
  exact (lp_norm_interpolation ν q₀ q₁ q θ hθ₀ hθ₁ hq (T f)
    (T f).aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ₁.le) h₀f.eLpNorm_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg hθ₀.le h₁f.eLpNorm_ne_top))

namespace SimpleInterpolation

lemma interpolationParam_center_of_interpolates
    (p₀ p₁ p : ℝ≥0∞) (θ : ℝ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0)
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hp : Interpolates p₀ p₁ p θ) :
    interpolationParam p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal (θ : ℂ) = 1 := by
  apply interpolationParam_center
  · exact ENNReal.toReal_ne_zero.mpr ⟨hpz, hpt⟩
  · simpa only [ENNReal.toReal_inv] using
      (interpolates_inverse_toReal p₀ p₁ p θ hθ₀ hθ₁ hp₀ hp₁ hp).symm

lemma finitePowerFamily_center
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : finiteSimpleSubmodule μ) (p₀ p₁ p : ℝ≥0∞) (θ : ℝ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0)
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hp : Interpolates p₀ p₁ p θ) :
    finitePowerFamily μ s
      (interpolationParam p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal (θ : ℂ)) = s := by
  rw [interpolationParam_center_of_interpolates p₀ p₁ p θ hθ₀ hθ₁ hp₀ hp₁ hpz hpt hp]
  apply Subtype.ext
  exact powerFamily_one s.val

end SimpleInterpolation


@[simp] theorem eLpNorm_finiteSimpleToSum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ r : ℝ≥0∞) (s : finiteSimpleSubmodule μ) :
    eLpNorm ((finiteSimpleToSum μ p₀ p₁ s : SumSpace μ p₀ p₁) : X →ₘ[μ] ℂ) r μ =
      eLpNorm s.val r μ := by
  exact eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)

@[simp] theorem finiteSimpleToSum_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ r : ℝ≥0∞) (s : finiteSimpleSubmodule μ) :
    MemLp ((finiteSimpleToSum μ p₀ p₁ s : SumSpace μ p₀ p₁) : X →ₘ[μ] ℂ) r μ :=
  (finiteSimple_memLp μ s r).ae_eq (AEEqFun.coeFn_mk _ _).symm

namespace SimpleInterpolation
@[simp] lemma finitePowerFamily_val {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : finiteSimpleSubmodule μ) (w : ℂ) :
    (finitePowerFamily μ s w).val = powerFamily s.val w := rfl
@[simp] lemma finitePowerFamily_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : finiteSimpleSubmodule μ) :
    finitePowerFamily μ s 1 = s := Subtype.ext (powerFamily_one s.val)

lemma finitePowerFamily_left_le_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : finiteSimpleSubmodule μ) (p₀ p₁ p : ℝ≥0∞)
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hp₀ : p₀ ≠ 0)
    (hs : eLpNorm s.val p μ ≤ 1) (t : ℝ) :
    eLpNorm (finitePowerFamily μ s (interpolationParam p.toReal
      (p₀⁻¹).toReal (p₁⁻¹).toReal ((t : ℂ) * Complex.I))).val p₀ μ ≤ 1 :=
  eLpNorm_powerFamily_endpoint_le_one s.val μ p p₀ hpz hpt hp₀ hs _
    (interpolationParam_left _ _ _ t)

lemma finitePowerFamily_right_le_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : finiteSimpleSubmodule μ) (p₀ p₁ p : ℝ≥0∞)
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hp₁ : p₁ ≠ 0)
    (hs : eLpNorm s.val p μ ≤ 1) (t : ℝ) :
    eLpNorm (finitePowerFamily μ s (interpolationParam p.toReal
      (p₀⁻¹).toReal (p₁⁻¹).toReal (1 + (t : ℂ) * Complex.I))).val p₁ μ ≤ 1 :=
  eLpNorm_powerFamily_endpoint_le_one s.val μ p p₁ hpz hpt hp₁ hs _
    (interpolationParam_right _ _ _ t)

end SimpleInterpolation

namespace NormDetection
variable {X : Type u} [MeasurableSpace X]

theorem integral_simple_bound_of_unit_bound (μ : Measure X)
    (p : ℝ≥0∞) (hpz : p ≠ 0) (hpt : p ≠ ∞) (g : X → ℂ) (C : ℝ)
    (htest : ∀ s : SimpleFunc X ℂ, s.FinMeasSupp μ → eLpNorm s p μ ≤ 1 →
      ‖∫ x, s x * g x ∂μ‖ ≤ C)
    (s : SimpleFunc X ℂ) (hs : s.FinMeasSupp μ) :
      ‖∫ x, s x * g x ∂μ‖ ≤ C * (eLpNorm s p μ).toReal := by
  have hmem : MemLp s p μ := (SimpleFunc.memLp_iff_finMeasSupp hpz hpt).mpr hs
  by_cases hn : eLpNorm s p μ = 0
  · have hae : (s : X → ℂ) =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hpz).mp hn
    have hi : (∫ x, s x * g x ∂μ) = 0 := by
      calc
        _ = ∫ x, (0 : ℂ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hae] with x hx
          simp [hx]
        _ = 0 := by simp
    simp [hi, hn]
  let a : ℂ := ((eLpNorm s p μ).toReal : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hn, hmem.eLpNorm_ne_top⟩)
  have han : ‖a‖ₑ = eLpNorm s p μ := by
    rw [← ofReal_norm]
    simp only [a, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  let t : SimpleFunc X ℂ := a⁻¹ • s
  have ht : t.FinMeasSupp μ := by
    rw [show t = s.map (a⁻¹ • ·) from SimpleFunc.smul_eq_map _ _]
    exact hs.map (smul_zero _)
  have htnorm : eLpNorm t p μ ≤ 1 := by
    change eLpNorm (a⁻¹ • (s : X → ℂ)) p μ ≤ 1
    rw [eLpNorm_const_smul, enorm_inv ha, han,
      ENNReal.inv_mul_cancel hn hmem.eLpNorm_ne_top]
  have hi : (∫ x, s x * g x ∂μ) = a * ∫ x, t x * g x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp [t, mul_assoc, ha]
  rw [hi, norm_mul]
  calc
    ‖a‖ * ‖∫ x, t x * g x ∂μ‖ ≤ ‖a‖ * C :=
      mul_le_mul_of_nonneg_left (htest t ht htnorm) (norm_nonneg a)
    _ = C * (eLpNorm s p μ).toReal := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg, mul_comm]

theorem norm_le_of_simple_unit_tests (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ∞)
    (g : Lp ℂ q μ) (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ s : SimpleFunc X ℂ, s.FinMeasSupp μ → eLpNorm s p μ ≤ 1 →
      ‖∫ x, s x * g x ∂μ‖ ≤ C) : ‖g‖ ≤ C := by
  apply norm_le_of_simple_tests μ p q hp g C hC
  exact integral_simple_bound_of_unit_bound μ p
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp g C htest

theorem norm_one_le_of_unit_tests (μ : Measure X) (g : Lp ℂ 1 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ h : Lp ℂ ∞ μ, ‖h‖ ≤ 1 → ‖∫ x, h x * g x ∂μ‖ ≤ C) : ‖g‖ ≤ C := by
  let L := D11.Ch20.IntegralPairing.pairing μ ∞ 1 g
  have hLn : ‖L‖ ≤ C := ContinuousLinearMap.opNorm_le_of_unit_norm hC (by
    intro h hn
    change ‖Specs.D11.Ch20.IntegralPairing.pairing_value μ ∞ 1 g h‖ ≤ C
    rw [(D11.Ch20.IntegralPairing.pairing_eq_integral μ ∞ 1 g h).2]
    exact htest h hn.le)
  exact (D11.Ch20.PairingNormFiniteQ.norm_pairing_one μ g).symm.trans_le hLn


end NormDetection
open SimpleInterpolation in

theorem simple_pairing_interpolation_normalized
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    (p₀ p₁ q₀ q₁ p r₀ r₁ r : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [ENNReal.HolderConjugate q₀ r₀] [ENNReal.HolderConjugate q₁ r₁]
    (θ M₀ M₁ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hp : Interpolates p₀ p₁ p θ) (hr : Interpolates r₀ r₁ r θ)
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hrz : r ≠ 0) (hrt : r ≠ ∞)
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (s : finiteSimpleSubmodule μ) (h : finiteSimpleSubmodule ν)
    (hs : eLpNorm s.val p μ ≤ 1) (hh : eLpNorm h.val r ν ≤ 1) :
    ‖sumFiniteSimplePairing T h₀ h₁ (finiteSimpleToSum μ p₀ p₁ s) h‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  classical
  have hp₀z : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁z : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  have hr₀z : r₀ ≠ 0 := ENNReal.HolderConjugate.ne_zero r₀ q₀
  have hr₁z : r₁ ≠ 0 := ENNReal.HolderConjugate.ne_zero r₁ q₁
  let fp := fun z => finitePowerFamily μ s
    (interpolationParam p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal z)
  let hp' := fun z => finitePowerFamily ν h
    (interpolationParam r.toReal (r₀⁻¹).toReal (r₁⁻¹).toReal z)
  let B := sumFiniteSimplePairing T h₀ h₁
  have hfl (t : ℝ) : eLpNorm
      ((finiteSimpleToSum μ p₀ p₁ (fp ((t : ℂ) * Complex.I))) : X →ₘ[μ] ℂ) p₀ μ ≤ 1 := by
    rw [finiteSimpleToSum_coe]
    calc
      _ = eLpNorm (fp ((t : ℂ) * Complex.I)).val p₀ μ :=
        eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)
      _ ≤ 1 := eLpNorm_powerFamily_endpoint_le_one s.val μ p p₀ hpz hpt hp₀z hs _
        (interpolationParam_left _ _ _ t)
  have hfr (t : ℝ) : eLpNorm
      ((finiteSimpleToSum μ p₀ p₁ (fp (1 + (t : ℂ) * Complex.I))) : X →ₘ[μ] ℂ) p₁ μ ≤ 1 := by
    rw [finiteSimpleToSum_coe]
    calc
      _ = eLpNorm (fp (1 + (t : ℂ) * Complex.I)).val p₁ μ :=
        eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)
      _ ≤ 1 := eLpNorm_powerFamily_endpoint_le_one s.val μ p p₁ hpz hpt hp₁z hs _
        (interpolationParam_right _ _ _ t)
  have hhl (t : ℝ) : eLpNorm (hp' ((t : ℂ) * Complex.I)).val r₀ ν ≤ 1 := by
    exact eLpNorm_powerFamily_endpoint_le_one h.val ν r r₀ hrz hrt hr₀z hh _
      (interpolationParam_left _ _ _ t)
  have hhr (t : ℝ) : eLpNorm (hp' (1 + (t : ℂ) * Complex.I)).val r₁ ν ≤ 1 := by
    exact eLpNorm_powerFamily_endpoint_le_one h.val ν r r₁ hrz hrt hr₁z hh _
      (interpolationParam_right _ _ _ t)
  have hleft (t : ℝ) :
      ‖B (finiteSimpleToSum μ p₀ p₁ (fp ((t : ℂ) * Complex.I)))
        (hp' ((t : ℂ) * Complex.I))‖ ≤ M₀ := by
    apply sumFiniteSimplePairing_endpoint_le T h₀ h₁ h₀ hM₀ _ _ _ (hfl t) (hhl t)
    exact (hfl t).trans_lt (by simp)
  have hright (t : ℝ) :
      ‖B (finiteSimpleToSum μ p₀ p₁ (fp (1 + (t : ℂ) * Complex.I)))
        (hp' (1 + (t : ℂ) * Complex.I))‖ ≤ M₁ := by
    apply sumFiniteSimplePairing_endpoint_le T h₀ h₁ h₁ hM₁ _ _ _ (hfr t) (hhr t)
    exact (hfr t).trans_lt (by simp)
  have hbound :
      ‖B (finiteSimpleToSum μ p₀ p₁ (fp (θ : ℂ))) (hp' (θ : ℂ))‖ ≤
        M₀ ^ (1 - θ) * M₁ ^ θ := by
    simp only [fp, hp'] at hleft hright ⊢
    simp only [finitePowerFamily_sum_domain] at hleft hright ⊢
    simp only [finitePowerFamily_eq_sum] at hleft hright ⊢
    exact three_lines_bilinear_exponential_sum s.val.range h.val.range B
      (fun c => finiteSimpleToSum μ p₀ p₁ (finitePowerAtom μ s c))
      (fun c => finitePowerAtom ν h c)
      (fun c => Real.log ‖c‖ * p.toReal * ((p₁⁻¹).toReal - (p₀⁻¹).toReal))
      (fun c => ((Real.log ‖c‖ * (p.toReal * (p₀⁻¹).toReal - 1) : ℝ) : ℂ))
      (fun c => Real.log ‖c‖ * r.toReal * ((r₁⁻¹).toReal - (r₀⁻¹).toReal))
      (fun c => ((Real.log ‖c‖ * (r.toReal * (r₀⁻¹).toReal - 1) : ℝ) : ℂ))
      M₀ M₁ θ hleft hright hθ₀ hθ₁
  have hpc : interpolationParam p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal (θ : ℂ) = 1 := by
    apply interpolationParam_center _ _ _ _ (ENNReal.toReal_ne_zero.mpr ⟨hpz, hpt⟩)
    rw [← interpolates_inverse_toReal p₀ p₁ p θ hθ₀.le hθ₁.le hp₀z hp₁z hp,
      ENNReal.toReal_inv]
  have hrc : interpolationParam r.toReal (r₀⁻¹).toReal (r₁⁻¹).toReal (θ : ℂ) = 1 := by
    apply interpolationParam_center _ _ _ _ (ENNReal.toReal_ne_zero.mpr ⟨hrz, hrt⟩)
    rw [← interpolates_inverse_toReal r₀ r₁ r θ hθ₀.le hθ₁.le hr₀z hr₁z hr,
      ENNReal.toReal_inv]
  have hfs : fp (θ : ℂ) = s := by
    dsimp [fp]
    rw [hpc]
    exact Subtype.ext (powerFamily_one s.val)
  have hhs : hp' (θ : ℂ) = h := by
    dsimp [hp']
    rw [hrc]
    exact Subtype.ext (powerFamily_one h.val)
  simpa only [hfs, hhs] using hbound



/-- Unit simple integral tests detect the full simple-input bound. -/
theorem simpleInputBound_of_pairing_unit_bound
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p₁ q₀ q₁ p q r : ℝ≥0∞} {M₀ M₁ θ C : ℝ}
    [Fact (1 ≤ r)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate r q]
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hrt : r ≠ ∞)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hq : Interpolates q₀ q₁ q θ)
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (hC : 0 ≤ C)
    (hpair : ∀ s : finiteSimpleSubmodule μ, eLpNorm s.val p μ ≤ 1 →
      ∀ h : finiteSimpleSubmodule ν, eLpNorm h.val r ν ≤ 1 →
        ‖∫ y, T (finiteSimpleToSum μ p₀ p₁ s) y * h.val y ∂ν‖ ≤ C) :
    SimpleInputBound T p q C := by
  apply simpleInputBound_of_unit_bound hpz hpt T C
  intro s hs hsdom hsn
  let S : finiteSimpleSubmodule μ := ⟨s, hs⟩
  have hmem := finiteSimple_output_memLp T h₀ h₁ hθ₀ hθ₁ hq S
  let g : Lp ℂ q ν := hmem.toLp _
  have hgn : ‖g‖ ≤ C := by
    apply NormDetection.norm_le_of_simple_unit_tests ν r q hrt g C hC
    intro h hh hhn
    calc
      ‖∫ y, h y * g y ∂ν‖ =
          ‖∫ y, T (finiteSimpleToSum μ p₀ p₁ S) y * h y ∂ν‖ := by
            congr 1
            apply integral_congr_ae
            filter_upwards [hmem.coeFn_toLp] with y hy
            simp only [g] at hy ⊢
            rw [hy, mul_comm]
      _ ≤ C := hpair S hsn ⟨h, hh⟩ hhn
  change eLpNorm (T (finiteSimpleToSum μ p₀ p₁ S)) q ν ≤ _
  apply (ENNReal.toReal_le_toReal hmem.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
  simpa only [g, Lp.norm_toLp, ENNReal.toReal_ofReal hC] using hgn



/-- When both target endpoints are L1, the original sum-domain map takes values in L1. -/
theorem sum_output_memLp_one
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁)
    (f : SumSpace μ p₀ p₁) : MemLp (T f) 1 ν := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp f.property
  let A : SumSpace μ p₀ p₁ := ⟨a, Submodule.mem_sup_left ha⟩
  let B : SumSpace μ p₀ p₁ := ⟨b, Submodule.mem_sup_right hb⟩
  have hA : MemLp (T A) 1 ν := (h₀ A (Lp.mem_Lp_iff_memLp.mp ha)).1
  have hB : MemLp (T B) 1 ν := (h₁ B (Lp.mem_Lp_iff_memLp.mp hb)).1
  have hAB : A + B = f := Subtype.ext hab
  apply (hA.add hB).ae_eq
  rw [← hAB, map_add]
  exact (AEEqFun.coeFn_add (T A) (T B)).symm

/-- This map retains precisely the original output a.e. class. -/
def sumToLone
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁) :
    SumSpace μ p₀ p₁ →ₗ[ℂ] Lp ℂ 1 ν where
  toFun f := ⟨T f, Lp.mem_Lp_iff_memLp.mpr (sum_output_memLp_one T h₀ h₁ f)⟩
  map_add' f g := Subtype.ext (T.map_add f g)
  map_smul' c f := Subtype.ext (T.map_smul c f)

@[simp] theorem sumToLone_coe
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁)
    (f : SumSpace μ p₀ p₁) :
    ((sumToLone T h₀ h₁ f : Lp ℂ 1 ν) : Y →ₘ[ν] ℂ) = T f := rfl

/-- Pairing with a fixed L-infinity class remains scalar linear. -/
def sumOnePairing
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁)
    (h : Lp ℂ ∞ ν) : SumSpace μ p₀ p₁ →ₗ[ℂ] ℂ :=
  (((D11.Ch20.IntegralPairing.pairing ν ∞ 1).flip h).toLinearMap).comp (sumToLone T h₀ h₁)

theorem sumOnePairing_eq_integral
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁)
    (h : Lp ℂ ∞ ν) (f : SumSpace μ p₀ p₁) :
    sumOnePairing T h₀ h₁ h f = ∫ y, h y * T f y ∂ν := by
  exact (D11.Ch20.IntegralPairing.pairing_eq_integral ν ∞ 1 (sumToLone T h₀ h₁ f) h).2

theorem sumOnePairing_endpoint_le
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ r : ℝ≥0∞} {M₀ M₁ M : ℝ}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁)
    (hT : EndpointBound T r 1 M) (hM : 0 ≤ M)
    (h : Lp ℂ ∞ ν) (hhn : ‖h‖ ≤ 1)
    (f : SumSpace μ p₀ p₁) (hf : MemLp (f : X →ₘ[μ] ℂ) r μ)
    (hfn : eLpNorm (f : X →ₘ[μ] ℂ) r μ ≤ 1) :
    ‖sumOnePairing T h₀ h₁ h f‖ ≤ M := by
  have hout : eLpNorm (T f) 1 ν ≤ ENNReal.ofReal M :=
    (hT f hf).2.trans (by simpa only [mul_one] using mul_le_mul' le_rfl hfn)
  have hnorm : ‖sumToLone T h₀ h₁ f‖ ≤ M := by
    rw [Lp.norm_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hout).trans_eq (ENNReal.toReal_ofReal hM)
  have hpair := D11.Ch20.IntegralPairing.norm_pairing_apply_le ν ∞ 1
    (sumToLone T h₀ h₁ f) h
  exact hpair.trans ((mul_le_of_le_one_right (norm_nonneg _) hhn).trans hnorm)

/-- A scalar linear functional on the finite input span obeys three lines. -/
theorem three_lines_linear_power_family
    {X : Type u} [MeasurableSpace X] (μ : Measure X) (p₀ p₁ : ℝ≥0∞)
    (s : finiteSimpleSubmodule μ) (L : SumSpace μ p₀ p₁ →ₗ[ℂ] ℂ)
    (P a b M₀ M₁ θ : ℝ)
    (hleft : ∀ t : ℝ, ‖L (finiteSimpleToSum μ p₀ p₁
      (SimpleInterpolation.finitePowerFamily μ s
        (SimpleInterpolation.interpolationParam P a b ((t : ℂ) * Complex.I))))‖ ≤ M₀)
    (hright : ∀ t : ℝ, ‖L (finiteSimpleToSum μ p₀ p₁
      (SimpleInterpolation.finitePowerFamily μ s
        (SimpleInterpolation.interpolationParam P a b (1 + (t : ℂ) * Complex.I))))‖ ≤ M₁)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ‖L (finiteSimpleToSum μ p₀ p₁
      (SimpleInterpolation.finitePowerFamily μ s
        (SimpleInterpolation.interpolationParam P a b (θ : ℂ))))‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  have heq (z : ℂ) : L (finiteSimpleToSum μ p₀ p₁
      (SimpleInterpolation.finitePowerFamily μ s (SimpleInterpolation.interpolationParam P a b z))) =
      ∑ c ∈ s.val.range, L (finiteSimpleToSum μ p₀ p₁ (SimpleInterpolation.finitePowerAtom μ s c)) *
        Complex.exp (((Real.log ‖c‖ * P * (b - a) : ℝ) : ℂ) * z +
          ((Real.log ‖c‖ * (P * a - 1) : ℝ) : ℂ)) := by
    rw [SimpleInterpolation.finitePowerFamily_sum_domain, map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  simp_rw [heq] at hleft hright ⊢
  exact three_lines_finite_exponential_sum s.val.range
    (fun c => L (finiteSimpleToSum μ p₀ p₁ (SimpleInterpolation.finitePowerAtom μ s c)))
    (fun c => ((Real.log ‖c‖ * (P * a - 1) : ℝ) : ℂ))
    (fun c => Real.log ‖c‖ * P * (b - a)) M₀ M₁ θ hleft hright hθ₀ hθ₁

theorem simpleInputBound_one
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (p₀ p₁ p : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    (θ M₀ M₁ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hp : Interpolates p₀ p₁ p θ) (hpt : p ≠ ∞)
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁) :
    SimpleInputBound T p 1 (M₀ ^ (1 - θ) * M₁ ^ θ) := by
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp₀z : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁z : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  apply simpleInputBound_of_unit_bound hpz hpt T
  intro s hs hsdom hsnorm
  let s' : finiteSimpleSubmodule μ := ⟨s, hs⟩
  let f := finiteSimpleToSum μ p₀ p₁ s'
  have hf : f = ⟨AEEqFun.mk s s.aestronglyMeasurable, hsdom⟩ := Subtype.ext rfl
  let g := sumToLone T h₀ h₁ f
  have hgnorm : ‖g‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
    apply NormDetection.norm_one_le_of_unit_tests ν g _ (by positivity)
    intro h hhnorm
    have hpair : (∫ y, h y * g y ∂ν) = sumOnePairing T h₀ h₁ h f :=
      (sumOnePairing_eq_integral T h₀ h₁ h f).symm
    rw [hpair]
    have hc := three_lines_linear_power_family μ p₀ p₁ s' (sumOnePairing T h₀ h₁ h)
      p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal M₀ M₁ θ ?_ ?_ hθ₀ hθ₁
    · simpa only [SimpleInterpolation.finitePowerFamily_center μ s' p₀ p₁ p θ
        hθ₀.le hθ₁.le hp₀z hp₁z hpz hpt hp] using hc
    · intro t
      apply sumOnePairing_endpoint_le T h₀ h₁ h₀ hM₀ h hhnorm
      · exact finiteSimpleToSum_memLp μ p₀ p₁ p₀ _
      · rw [eLpNorm_finiteSimpleToSum]
        exact SimpleInterpolation.finitePowerFamily_left_le_one μ s' p₀ p₁ p
          hpz hpt hp₀z hsnorm t
    · intro t
      apply sumOnePairing_endpoint_le T h₀ h₁ h₁ hM₁ h hhnorm
      · exact finiteSimpleToSum_memLp μ p₀ p₁ p₁ _
      · rw [eLpNorm_finiteSimpleToSum]
        exact SimpleInterpolation.finitePowerFamily_right_le_one μ s' p₀ p₁ p
          hpz hpt hp₁z hsnorm t
  rw [← hf]
  have heq : eLpNorm (T f) 1 ν = ENNReal.ofReal ‖g‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)]
    rfl
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hgnorm



/-- The sharp simple-input estimate when the output conjugate exponent is finite. -/
theorem riesz_thorin_simple_estimate_ne_one
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite ν]
    (p₀ p₁ q₀ q₁ p q : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (θ M₀ M₁ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hp : Interpolates p₀ p₁ p θ) (hq : Interpolates q₀ q₁ q θ)
    (hpt : p ≠ ∞) (hq1 : q ≠ 1)
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁) :
    SimpleInputBound T p q (M₀ ^ (1 - θ) * M₁ ^ θ) := by
  let r₀ := ENNReal.conjExponent q₀
  let r₁ := ENNReal.conjExponent q₁
  let r := ENNReal.conjExponent q
  have : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r q⟩
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hrz : r ≠ 0 := ENNReal.HolderConjugate.ne_zero r q
  have hrt : r ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one r q).mpr hq1
  have hr : Interpolates r₀ r₁ r θ :=
    interpolates_conjugates q₀ q₁ q r₀ r₁ r θ hθ₀.le hθ₁.le hq
  apply simpleInputBound_of_pairing_unit_bound (r := r) hpz hpt hrt hθ₀ hθ₁ hq
    T h₀ h₁ (by positivity)
  intro s hs h hh
  exact simple_pairing_interpolation_normalized μ ν p₀ p₁ q₀ q₁ p r₀ r₁ r
    θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hp hr hpz hpt hrz hrt T h₀ h₁ s h hs hh


/-- Riesz--Thorin's sharp estimate on finite-support simple inputs, including target L1. -/
theorem riesz_thorin_simple_estimate : SimpleEstimate.{u,v} := by
  intro X Y _ _ μ ν _ _ p₀ p₁ q₀ q₁ p q _ _ _ _ _ _ θ M₀ M₁
    hθ₀ hθ₁ hM₀ hM₁ hp hq hpt T h₀ h₁
  by_cases hqone : q = 1
  · subst q
    obtain ⟨rfl, rfl⟩ := (interpolates_one_iff q₀ q₁ θ hθ₀ hθ₁).mp hq
    exact simpleInputBound_one μ ν p₀ p₁ p θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hp hpt T h₀ h₁
  · exact riesz_thorin_simple_estimate_ne_one μ ν p₀ p₁ q₀ q₁ p q
      θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hp hq hpt hqone T h₀ h₁

/-- The original common-domain operator satisfies the full sharp interpolation bound. -/
theorem riesz_thorin : RieszThorin.{u,v} :=
  riesz_thorin_of_simple_estimate riesz_thorin_simple_estimate

end ExpandedFA.Interpolation
