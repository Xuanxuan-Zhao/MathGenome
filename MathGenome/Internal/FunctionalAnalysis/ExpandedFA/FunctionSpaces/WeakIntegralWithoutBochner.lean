import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.WeakIntegralWithoutBochner
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Lemmas

noncomputable section
open Filter MeasureTheory
open ExpandedFA.P1.C01SequenceSpaces
open scoped ENNReal Topology
universe u

namespace ExpandedFA.FunctionSpaces.WeakIntegralWithoutBochner

lemma harmonic_coordinates_mem (𝕜 : Type u) [RCLike 𝕜] :
    Memℓp (fun n : ℕ => ((n + 1 : ℕ) : 𝕜)⁻¹) 2 := by
  apply memℓp_gen
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) := by
    exact (Real.summable_nat_pow_inv).mpr (by decide)
  have hs := (summable_nat_add_iff 1).mpr h
  simpa only [norm_inv, RCLike.norm_natCast, ENNReal.toReal_ofNat,
    Real.rpow_two, inv_pow] using hs

lemma harmonic_term_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ‖harmonicTerm 𝕜 n‖ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [harmonicTerm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simp only [norm_inv, RCLike.norm_natCast]

lemma harmonic_norm_not_summable (𝕜 : Type u) [RCLike 𝕜] :
    ¬ Summable (fun n => ‖harmonicTerm 𝕜 n‖) := by
  simp_rw [harmonic_term_norm]
  exact fun h => Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp h)

theorem weak_integral_without_bochner : Spec.Counterexample.{u} := by
  intro 𝕜 _
  let I : SequenceLp 𝕜 2 := ⟨_, harmonic_coordinates_mem 𝕜⟩
  have hsum : HasSum (harmonicTerm 𝕜) I := lp.hasSum_single (by simp) I
  have hnot := harmonic_norm_not_summable 𝕜
  have hni : ¬ Integrable (harmonicTerm 𝕜) Measure.count := by
    rwa [integrable_count_iff]
  refine ⟨I, fun _ => rfl, hsum, ?_, ?_, harmonic_term_norm 𝕜, hnot, ?_, ?_⟩
  · apply (strongMeasurable_identification Measure.count (harmonicTerm 𝕜)).mpr
    exact (StronglyMeasurable.of_discrete : StronglyMeasurable (harmonicTerm 𝕜)).aestronglyMeasurable
  · intro L
    have hs : HasSum (fun n => L (harmonicTerm 𝕜 n)) (L I) := L.hasSum hsum
    have habs : Summable (fun n => ‖L (harmonicTerm 𝕜 n)‖) := hs.summable.norm
    have hi : Integrable (fun n => L (harmonicTerm 𝕜 n)) Measure.count :=
      integrable_count_iff.mpr habs
    refine ⟨habs, hi, ?_⟩
    rw [integral_countable hi]
    simpa using hs.tsum_eq.symm
  · by_contra hfin
    apply hni
    exact ⟨(StronglyMeasurable.of_discrete : StronglyMeasurable (harmonicTerm 𝕜)).aestronglyMeasurable,
      lt_of_le_of_ne le_top hfin⟩
  · exact fun h => hni ((bochnerIntegrable_identification Measure.count _).mp h)

end ExpandedFA.FunctionSpaces.WeakIntegralWithoutBochner
