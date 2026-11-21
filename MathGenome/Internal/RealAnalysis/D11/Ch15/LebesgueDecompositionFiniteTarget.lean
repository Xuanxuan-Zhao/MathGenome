import MathGenome.Internal.RealAnalysis.D11.Ch15.ACSingularZero
import MathGenome.Internal.RealAnalysis.D11.Ch14.VariationInequalities
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import Mathlib.Topology.Order.IsLUB
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.LebesgueDecompositionFiniteTarget

/-! Finite-target decomposition relative to an arbitrary positive measure.
The reference measure has no size or completeness hypothesis. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace D11.Ch15.LebesgueDecompositionFiniteTarget

open D11.Ch14.ScalarInterfaces D11.Ch14.TotalVariation
open D11.Ch14.VariationInequalities D11.Ch15.AbsoluteContinuity

/-- Countable unions attain the supremum of the masses of measurable null sets.
This preliminary assertion does not require even the target to be finite. -/
theorem exists_maximal_null_set {α : Type u} [MeasurableSpace α]
    (ρ μ : Measure α) :
    ∃ B, MeasurableSet B ∧ μ B = 0 ∧
      ∀ E, MeasurableSet E → μ E = 0 → ρ E ≤ ρ B := by
  classical
  let S : Set ℝ≥0∞ := {r | ∃ E, MeasurableSet E ∧ μ E = 0 ∧ ρ E = r}
  have hS : S.Nonempty := ⟨0, ∅, MeasurableSet.empty, measure_empty,
    measure_empty⟩
  obtain ⟨r, _, hr, hmem⟩ := exists_seq_tendsto_sSup hS (OrderTop.bddAbove S)
  choose E hE hnull hmass using hmem
  let B := ⋃ n, E n
  have hB : MeasurableSet B := MeasurableSet.iUnion hE
  have hμB : μ B = 0 := measure_iUnion_null hnull
  have hsup : sSup S ≤ ρ B := by
    apply le_of_tendsto' hr
    intro n
    rw [← hmass n]
    exact measure_mono (subset_iUnion E n)
  refine ⟨B, hB, hμB, ?_⟩
  intro A hA hμA
  exact (le_sSup (show ρ A ∈ S from ⟨A, hA, hμA, rfl⟩)).trans hsup

/-- Maximality and finite target mass force the remaining restriction to be AC. -/
theorem null_difference {α : Type u} [MeasurableSpace α]
    (ρ μ : Measure α) [IsFiniteMeasure ρ] (B : Set α)
    (hB : MeasurableSet B) (hμB : μ B = 0)
    (hmax : ∀ E, MeasurableSet E → μ E = 0 → ρ E ≤ ρ B)
    (E : Set α) (hE : MeasurableSet E) (hμE : μ E = 0) :
    ρ (E \ B) = 0 := by
  have hle := hmax (B ∪ E) (hB.union hE) (measure_union_null hμB hμE)
  have hsplit : ρ (B ∪ E) = ρ B + ρ (E \ B) := by
    rw [← union_sdiff_self (s := B) (t := E)]
    exact measure_union disjoint_sdiff_right (hE.diff hB)
  rw [hsplit] at hle
  exact le_zero_iff.mp ((ENNReal.add_le_add_iff_left (measure_ne_top ρ B)).mp
    (by simpa only [add_zero] using hle))

theorem restrict_finite_variation {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    [IsFiniteMeasure (totalVariation ν)] (B : Set α) (hB : MeasurableSet B) :
    IsFiniteMeasure (totalVariation (ν.restrict B)) := by
  change IsFiniteMeasure (ν.restrict B).variation
  rw [VectorMeasure.variation_restrict hB]
  change IsFiniteMeasure ((totalVariation ν).restrict B)
  infer_instance

/-- Restriction to a maximal reference-null set and its complement gives the
two finite parts. Uniqueness is the upstream AC/singular-zero argument. -/
theorem finite_variation_decomposition :
    Specs.D11.Ch15.LebesgueDecompositionFiniteTarget.finite_variation_decomposition.{u,v} := by
  intro α _ K _ ν μ hfin
  change IsFiniteMeasure (totalVariation ν) at hfin
  obtain ⟨B, hB, hμB, hmax⟩ := exists_maximal_null_set (totalVariation ν) μ
  have hsum : ν = ν.restrict Bᶜ + ν.restrict B := by
    rw [add_comm]
    exact (VectorMeasure.restrict_add_restrict_compl hB).symm
  have hac : scalarAbsolutelyContinuous (ν.restrict Bᶜ) μ := by
    apply (scalar_iff _ _).mpr
    intro E hE hμE
    rw [VectorMeasure.restrict_apply ν hB.compl hE]
    apply (totalVariation_null_iff ν (E \ B) (hE.diff hB)).mp
      (null_difference (totalVariation ν) μ B hB hμB hmax E hE hμE)
      (E ∩ Bᶜ) (hE.inter hB.compl)
    exact Set.Subset.rfl
  have hsing : scalarPositiveSingular (ν.restrict B) μ := by
    refine ⟨B, hB, ?_, hμB⟩
    rw [← totalVariation_apply _ _ hB.compl,
      variation_restrict ν B Bᶜ hB hB.compl, compl_inter_self, measure_empty]
  refine ⟨B, ⟨hB, hμB, hmax⟩, restrict_finite_variation ν Bᶜ hB.compl,
    restrict_finite_variation ν B hB, hsum, hac, hsing, ?_⟩
  intro a s heq ha hs
  exact ACSingularZero.decomposition_unique ν μ a s (ν.restrict Bᶜ) (ν.restrict B)
    heq hsum ha hs hac hsing

theorem signed_decomposition :
    Specs.D11.Ch15.LebesgueDecompositionFiniteTarget.signed_decomposition.{u} := by
  intro α _ ν μ
  have : IsFiniteMeasure (Specs.D11.Ch14.TotalVariation.totalVariation_value ν) :=
    signed_finite ν
  obtain ⟨B, hB, hdecomp⟩ := finite_variation_decomposition ν μ
  refine ⟨B, hB, hdecomp, ?_⟩
  intro hpos E hE
  rw [VectorMeasure.restrict_apply ν hB.1.compl hE,
    VectorMeasure.restrict_apply ν hB.1 hE]
  exact ⟨hpos _ (hE.inter hB.1.compl), hpos _ (hE.inter hB.1)⟩

theorem complex_decomposition :
    Specs.D11.Ch15.LebesgueDecompositionFiniteTarget.complex_decomposition.{u} := by
  intro α _ ν μ
  have : IsFiniteMeasure (Specs.D11.Ch14.TotalVariation.totalVariation_value ν) :=
    complex_finite ν
  obtain ⟨B, hB, hdecomp⟩ := finite_variation_decomposition ν μ
  refine ⟨B, hB, hdecomp, ?_⟩
  intro hpos E hE
  rw [VectorMeasure.restrict_apply ν hB.1.compl hE,
    VectorMeasure.restrict_apply ν hB.1 hE]
  exact ⟨hpos _ (hE.inter hB.1.compl), hpos _ (hE.inter hB.1)⟩

end D11.Ch15.LebesgueDecompositionFiniteTarget
