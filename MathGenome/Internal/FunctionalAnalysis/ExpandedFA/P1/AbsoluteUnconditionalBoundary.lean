import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.AbsoluteUnconditionalBoundary
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15Unconditional
import Mathlib.Analysis.PSeries

/-!
Absolute norm summability gives convergence of the finite-subset net in a
complete normed group. For the strict converse boundary, the scalar sequence
`1/(n+1)` lies in canonical ℓ² by the p-series theorem. Its coordinate-vector
expansion converges unconditionally by `lp.hasSum_single`, whereas the norms
of those vectors are exactly the terms of the divergent harmonic series.
-/

noncomputable section
open Filter
open scoped Topology ENNReal

namespace ExpandedFA.P1.AbsoluteUnconditionalBoundary

open C01SequenceSpaces

abbrev harmonicTerms : Spec.HarmonicTermType := Spec.HarmonicTermValue

theorem absolute_implies_unconditional : Spec.AbsoluteImpliesUnconditional := by
  intro E _ _ v hv
  exact (C15Unconditional.unconditionallyConvergent_iff_summable v).mpr hv.of_norm

theorem harmonic_coordinates : Spec.HarmonicCoordinates := by
  intro 𝕜 _ n j
  simp only [harmonicTerm, lp.single_apply, Pi.single_apply]

theorem harmonic_norm : Spec.HarmonicNorm := by
  intro 𝕜 _ n
  simpa only [harmonicTerm, norm_inv, RCLike.norm_natCast] using
    lp.norm_single (E := fun _ : ℕ => 𝕜) (p := 2)
      (by norm_num : 0 < (2 : ℝ≥0∞)) n (((n + 1 : ℕ) : 𝕜)⁻¹)

/-- The sequence whose coordinate expansion is the required series belongs
to ℓ², because the sum of its squared coordinate norms is a p-series. -/
theorem harmonic_mem_lp (𝕜 : Type*) [RCLike 𝕜] :
    Memℓp (fun n : ℕ => (((n + 1 : ℕ) : 𝕜)⁻¹)) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
    (summable_nat_add_iff 1).mpr
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  simpa only [norm_inv, RCLike.norm_natCast, ENNReal.toReal_ofNat,
    Real.rpow_two, inv_pow] using hs

theorem harmonic_boundary : Spec.HarmonicBoundary := by
  intro 𝕜 _
  let x : SequenceLp 𝕜 2 := ⟨_, harmonic_mem_lp 𝕜⟩
  have hx : HasSum (harmonicTerm 𝕜) x :=
    lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x
  refine ⟨⟨x, (C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mpr hx⟩, ?_, ?_⟩
  · change ¬ Summable (fun n => ‖harmonicTerm 𝕜 n‖)
    simp_rw [harmonic_norm 𝕜]
    exact fun h => Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp h)
  · simpa only [harmonic_norm 𝕜, Nat.cast_add, Nat.cast_one, one_div] using
      Real.tendsto_sum_range_one_div_nat_succ_atTop

end ExpandedFA.P1.AbsoluteUnconditionalBoundary
