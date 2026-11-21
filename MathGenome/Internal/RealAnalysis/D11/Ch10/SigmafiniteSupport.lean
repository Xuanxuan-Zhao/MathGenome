import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.SigmafiniteSupport
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch10.Chebyshev
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions

/-! Sigma-finite nonzero support of raw finite-p functions, on arbitrary
positive measures. The cover and its estimate are pointwise and use the
original measure, without passing to an a.e. representative or completion. -/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace D11.Ch10.SigmafiniteSupport

theorem support_eq_iUnion : Specs.D11.Ch10.SigmafiniteSupport.support_eq_iUnion := by
  intro X E _ f
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hx
    exact exists_nat_one_div_lt (norm_pos_iff.mpr hx)
  · rintro ⟨n, hn⟩
    exact norm_pos_iff.mp ((one_div_pos.mpr (Nat.cast_add_one_pos n)).trans hn)

theorem level_measure_bound : Specs.D11.Ch10.SigmafiniteSupport.level_measure_bound := by
  intro X E _ _ _ _ μ p f hp hf n
  change f ∈ LpDefinition.rawLp μ p at hf
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hn0 : 0 < (n + 1 : ℝ) := Nat.cast_add_one_pos n
  have hC0 : ENNReal.ofReal ((n + 1 : ℝ) ^ p) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hn0 p)
  have hnorm : LpDefinition.powerNorm μ p f ^ p =
      D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ
        (fun x => ENNReal.ofReal (‖f x‖ ^ p)) := by
    unfold LpDefinition.powerNorm
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hcheb := Chebyshev.chebyshev μ f p (1 / (n + 1 : ℝ)) hf.1 hp0
    (one_div_pos.mpr hn0)
  change ENNReal.ofReal ((1 / (n + 1 : ℝ)) ^ p) *
    μ {x | 1 / (n + 1 : ℝ) < ‖f x‖} ≤
      D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ
        (fun x => ENNReal.ofReal (‖f x‖ ^ p)) at hcheb
  rw [one_div, Real.inv_rpow hn0.le,
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hn0 p)] at hcheb
  refine ⟨LpDefinition.measurable_strict_level f hf.1 _, ?_, ?_⟩
  · change μ _ ≤ ENNReal.ofReal _ * LpDefinition.powerNorm μ p f ^ p
    rw [hnorm]
    simpa only [one_div] using
      (ENNReal.inv_mul_le_iff hC0 ENNReal.ofReal_ne_top).mp hcheb
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp0.le hf.2.ne)

theorem sigmafinite_support : Specs.D11.Ch10.SigmafiniteSupport.sigmafinite_support := by
  intro X E _ _ _ _ μ p f hp hf
  have hU := support_eq_iUnion f
  change D11.Ch01.MeasureDefinitions.isSigmaFiniteSet μ {x | f x ≠ 0}
  have hlevel := level_measure_bound μ p f hp hf
  refine ⟨?_, (fun n : ℕ => {x | 1 / (n + 1 : ℝ) < ‖f x‖}), ?_, hU.symm⟩
  · rw [hU]
    exact MeasurableSet.iUnion fun n => (hlevel n).1
  · intro n
    refine ⟨(hlevel n).1, ?_, (hlevel n).2.1.trans_lt (hlevel n).2.2⟩
    intro x hx
    exact norm_pos_iff.mp ((one_div_pos.mpr (Nat.cast_add_one_pos n)).trans hx)

end D11.Ch10.SigmafiniteSupport
