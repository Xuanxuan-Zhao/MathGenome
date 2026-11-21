import MathGenome.Internal.RealAnalysis.D11.Ch14.ScalarInterfaces
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.NegativeExtraction
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn

/-! Negative-set extraction for arbitrary real-valued signed measures.
The library Hahn decomposition is already proved independently of this module.
Intersect its negative part with the given set; the discarded part has
nonnegative measure. -/

open Set MeasureTheory

universe u

namespace D11.Ch14.NegativeExtraction

open D11.Ch14.ScalarInterfaces

/-- `paper.tex`, lemma `d11:14:negative-extraction`. -/
theorem negative_extraction {α : Type u} [MeasurableSpace α]
    (ν : SignedMeasure α) (E : Set α) (hE : MeasurableSet E) :
    ∃ N : Set α, N ⊆ E ∧ negativeSet ν N ∧ ν N ≤ ν E := by
  obtain ⟨P, hP, hpos, hneg⟩ := ν.exists_compl_positive_negative
  refine ⟨E \ P, Set.sdiff_subset, ⟨hE.diff hP, ?_⟩, ?_⟩
  · intro A hA hAN
    have hAP : A ⊆ Pᶜ := fun _ hx => (hAN hx).2
    simpa using (VectorMeasure.restrict_le_restrict_iff ν 0 hP.compl).mp hneg hA hAP
  · have hnonneg : 0 ≤ ν (E ∩ P) := by
      simpa using (VectorMeasure.restrict_le_restrict_iff 0 ν hP).mp hpos
        (hE.inter hP) Set.inter_subset_right
    have hsplit : ν E = ν (E \ P) + ν (E ∩ P) := by
      simpa only [Set.sdiff_union_inter] using
        ν.of_union Set.disjoint_sdiff_inter (hE.diff hP) (hE.inter hP)
    calc
      ν (E \ P) ≤ ν (E \ P) + ν (E ∩ P) := le_add_of_nonneg_right hnonneg
      _ = ν E := hsplit.symm

end D11.Ch14.NegativeExtraction
