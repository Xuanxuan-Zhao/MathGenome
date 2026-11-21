import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.ResidueComputation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D12Complex.ResidueComputation
open Residue

/-- On every sufficiently small circle, cancellation of the pole factor
identifies the residue integral with a Cauchy derivative integral. -/
theorem residue_pole_formula :
    Specs.D12Complex.Ch08.ResidueComputation.residue_pole_formula_type := by
  intro f g a m U hm ha hg hfg
  obtain ⟨ε, hε, hE⟩ := Metric.mem_nhdsWithin_iff.mp hfg
  obtain ⟨δ, hδ, hU⟩ := Metric.mem_nhds_iff.mp (hg.1.mem_nhds ha)
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hε),
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ρ hρ hρε hρδ
  have hd : DifferentiableOn ℂ g (closedBall a ρ) := by
    intro z hz
    apply (hg.2 z (hU ?_)).differentiableWithinAt
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hρδ)
  have hc := hd.circleIntegral_one_div_sub_center_pow_smul hρ (m - 1)
  have hI : circleIntegral f a ρ =
      circleIntegral (fun z => (1 / (z-a)^((m-1)+1)) * g z) a ρ := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    have hza : z ≠ a := by
      intro h
      subst z
      have : (0 : ℝ) = ρ := by simpa using mem_sphere.mp hz
      exact (ne_of_gt hρ) this.symm
    have he : g z = (z-a)^m * f z :=
      hE ⟨mem_ball.mpr ((mem_sphere.mp hz).trans_lt hρε), hza⟩
    dsimp only
    rw [Nat.sub_add_cancel hm, he]
    field_simp [pow_ne_zero m (sub_ne_zero.mpr hza)]
  rw [hI]
  simp only [smul_eq_mul] at hc
  rw [hc]
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp

/-- A simple zero factors as `(z-a) * q₁ z`, with q₁(a)=q′(a).
This follows from the actual analytic order and local zero factorization. -/
private lemma factor_simple_zero (q : ℂ → ℂ) (a : ℂ) (U : Set ℂ)
    (ha : a ∈ U) (hq : HolomorphicOn U q) (hq0 : q a = 0)
    (hq' : deriv q a ≠ 0) :
    ∃ q₁ : ℂ → ℂ, LocalZeroFactorization.HolomorphicNear q₁ a ∧
      q₁ a = deriv q a ∧
      ∀ᶠ z in 𝓝 a, q z = (z-a) * q₁ z := by
  have hnear : LocalZeroFactorization.HolomorphicNear q a := ⟨U, ha, hq⟩
  have hana := (LocalZeroFactorization.holomorphicNear_iff_analyticAt q a).mp hnear
  have hord : LocalZeroFactorization.order q a = (1 : ℕ) :=
    hana.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hq0 hq'
  obtain ⟨q₁, hq₁, hq₁0, heq⟩ :=
    (LocalZeroFactorization.order_eq_nat_iff q a hnear 1).mp hord
  have heq' : q =ᶠ[𝓝 a] (fun z => (z-a) * q₁ z) := by
    change ∀ᶠ z in 𝓝 a, q z = (z-a) * q₁ z
    simpa only [pow_one] using heq
  have hd₁ := ((LocalZeroFactorization.holomorphicNear_iff_analyticAt q₁ a).mp
    hq₁).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun z => (z-a) * q₁ z) (q₁ a) a := by
    convert (((hasDerivAt_id a).sub_const a).fun_mul hd₁) using 1 <;> simp
  exact ⟨q₁, hq₁, (hd.congr_of_eventuallyEq heq').deriv.symm, heq'⟩

theorem residue_simple_quotient :
    Specs.D12Complex.Ch08.ResidueComputation.residue_simple_quotient_type := by
  intro f p q a U ha hp hq hq0 hq' hfq
  obtain ⟨q₁, hq₁, hq₁a, heq⟩ := factor_simple_zero q a U ha hq hq0 hq'
  have hpnear : LocalZeroFactorization.HolomorphicNear p a := ⟨U, ha, hp⟩
  have hpana := (LocalZeroFactorization.holomorphicNear_iff_analyticAt p a).mp hpnear
  have hq₁ana := (LocalZeroFactorization.holomorphicNear_iff_analyticAt q₁ a).mp hq₁
  have hgana : AnalyticAt ℂ (fun z => p z / q₁ z) a :=
    hpana.div hq₁ana (by simpa [hq₁a] using hq')
  obtain ⟨V, haV, hg⟩ :=
    (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ a).mpr hgana
  have hfg : ∀ᶠ z in 𝓝[≠] a, p z / q₁ z = (z-a)^1 * f z := by
    filter_upwards [hfq, heq.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hfz hqz hza
    rw [hfz, hqz, pow_one]
    have hz : z - a ≠ 0 := sub_ne_zero.mpr hza
    field_simp
  simpa [hq₁a] using residue_pole_formula f (fun z => p z / q₁ z) a 1 V
    (le_refl 1) haV hg hfg

end D12Complex.ResidueComputation
