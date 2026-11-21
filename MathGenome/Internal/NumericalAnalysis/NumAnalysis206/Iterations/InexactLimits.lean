import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.InexactLimits
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.InexactBound
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.ResidualCertificate
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

namespace NumAnalysis206.Iterations

universe u

open Filter
open scoped Topology

/-- Limit of the finite geometric majorant, valid also at `q = 0`. -/
lemma tendsto_inexact_majorant (q a ε : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => q ^ n * a + ε * (1 - q ^ n) / (1 - q))
      atTop (𝓝 (ε / (1 - q))) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  simpa using (hpow.mul_const a).add
    (((hpow.const_sub 1).const_mul ε).div_const (1 - q))

/-- W71: the real limsup is bounded by the common error divided by `1-q`. -/
theorem inexact_limsup_le :
    Specs.NumAnalysis206.Iterations.InexactLimits.CommonErrorLimsup := by
  intro X inst D T q p x δ ε hq hq1 hTD hcontract hp hfix hx herror hcommon
  have hbound := inexact_common_bound D T q p x δ ε hq hq1 hTD hcontract
    hp hfix hx herror hcommon
  have hlim := tendsto_inexact_majorant q (dist (x 0) p) ε hq hq1
  calc
    limsup (fun n => dist (x n) p) atTop ≤
        limsup (fun n => q ^ n * dist (x 0) p + ε * (1 - q ^ n) / (1 - q)) atTop :=
      limsup_le_limsup (Eventually.of_forall hbound)
        (isCoboundedUnder_le_of_le atTop (fun _ => dist_nonneg)) hlim.isBoundedUnder_le
    _ = ε / (1 - q) := hlim.limsup_eq

/-- W71: restart the finite estimate after the errors become small. The initial
restart distance absorbs all finitely many early errors and decays geometrically. -/
theorem inexact_tendsto_of_errors_tendsto_zero :
    Specs.NumAnalysis206.Iterations.InexactLimits.VanishingErrorConvergence := by
  intro X inst D T q p x δ hq hq1 hTD hcontract hp hfix hx herror hδ
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hsmall : 0 < (1 - q) * (ε / 2) := mul_pos hden (by linarith)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hδ.eventually_lt_const hsmall)
  have hcommon : ∀ j, δ (j + J) ≤ (1 - q) * (ε / 2) :=
    fun j => (hJ (j + J) (Nat.le_add_left _ _)).le
  have hshift : ∀ j, dist (x ((j + 1) + J)) (T (x (j + J))) ≤ δ (j + J) := by
    intro j
    simpa only [Nat.add_right_comm j 1 J] using (herror (j + J))
  have hbound := inexact_common_bound D T q p (fun j => x (j + J))
    (fun j => δ (j + J)) ((1 - q) * (ε / 2)) hq hq1 hTD hcontract hp hfix
    (fun j => hx (j + J)) hshift hcommon
  have hlim := tendsto_inexact_majorant q (dist (x J) p) ((1 - q) * (ε / 2)) hq hq1
  have hhalf : (1 - q) * (ε / 2) / (1 - q) = ε / 2 := by
    field_simp [ne_of_gt hden]
  rw [hhalf] at hlim
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (show ε / 2 < ε by linarith))
  refine ⟨N + J, fun n hn => ?_⟩
  have hnJ : J ≤ n := by omega
  have hnN : N ≤ n - J := by omega
  have hb := hbound (n - J)
  simp only [Nat.sub_add_cancel hnJ, Nat.zero_add] at hb
  exact hb.trans_lt (hN (n - J) hnN)

/-- W71's finite estimate, reused from the finite-estimate interface. -/
theorem inexact_limits_finite_convolution :
    Specs.NumAnalysis206.Iterations.InexactLimits.FiniteConvolution.{u} :=
  inexact_convolution_bound

/-- W71's finite common-error estimate. -/
theorem inexact_limits_finite_common_bound :
    Specs.NumAnalysis206.Iterations.InexactLimits.FiniteCommonBound.{u} :=
  inexact_common_bound

/-- W71's approximate-evaluation stopping consequence. -/
theorem inexact_limits_approximate_stopping :
    Specs.NumAnalysis206.Iterations.InexactLimits.ApproximateStopping.{u} :=
  approximate_residual_stopping

end NumAnalysis206.Iterations
