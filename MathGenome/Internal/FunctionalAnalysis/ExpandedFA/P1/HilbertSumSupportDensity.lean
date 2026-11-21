import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02HilbertSum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HilbertSumSupportDensity

/-! Countable support and finite-support density for Hilbert direct sums.
The proofs apply to the more general dependent `lp` of normed additive groups.
They use finite-subset sums throughout, with no enumeration of the index type.
-/

open scoped ENNReal Classical

noncomputable section

universe u v

namespace ExpandedFA.P1.HilbertSumSupportDensity

open ExpandedFA.P1.C02HilbertSum

variable {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]

/-- Summability of the squared norms forces countability of their support,
which is exactly the set of nonzero coordinates. -/
theorem countable_support (x : Space H) : Set.Countable {i | x i ≠ 0} := by
  have hs : Summable (fun i => ‖x i‖ ^ 2) := by
    simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).summable
  simpa only [Function.support, ne_eq, sq_eq_zero_iff, norm_eq_zero] using
    hs.countable_support

/-- Finite coordinate truncations converge along the directed set of all
finite subsets, including when the index type is uncountable. -/
theorem tendsto_truncate (x : Space H) :
    Filter.Tendsto (fun A : Finset I => truncate H A (fun i => x i))
      Filter.atTop (nhds x) := by
  classical
  simpa only [HasSum, SummationFilter.unconditional, truncate,
    ExpandedFA.P1.C02HilbertSum.Spec.truncate]
    using (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)

/-- In particular, some finite coordinate truncation achieves every positive
norm tolerance. -/
theorem exists_finite_truncation (x : Space H) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Finset I, ‖x - truncate H A (fun i => x i)‖ < ε := by
  obtain ⟨A, hA⟩ := (Metric.tendsto_nhds.mp (tendsto_truncate x) ε hε).exists
  exact ⟨A, by simpa only [dist_eq_norm, norm_sub_rev] using hA⟩

/-- The finite-support subset fixed by the direct-sum interface is dense. -/
theorem dense_finiteSupport (H : I → Type v) [∀ i, NormedAddCommGroup (H i)] :
    Dense (finiteSupport H) := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := exists_finite_truncation x ε hε
  exact ⟨truncate H A (fun i => x i), truncate_finiteSupport A _,
    by simpa only [dist_eq_norm] using hA⟩

end ExpandedFA.P1.HilbertSumSupportDensity
