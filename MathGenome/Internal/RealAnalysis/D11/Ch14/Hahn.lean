import MathGenome.Internal.RealAnalysis.D11.Ch14.ScalarInterfaces
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.Hahn
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn

/-! Hahn decomposition and uniqueness on every measurable subset of the
symmetric difference, with nullity for the raw partition variation.
Existence uses the library's independently proved real-valued Hahn theorem.
Uniqueness uses only signs, finite additivity, and the raw variation null test. -/

open Set MeasureTheory
open scoped symmDiff

universe u

namespace D11.Ch14.Hahn

open D11.Ch14.ScalarInterfaces

theorem hahn_exists {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) :
    ∃ P N : Set α, positiveSet ν P ∧ negativeSet ν N ∧
      Disjoint P N ∧ P ∪ N = univ := by
  obtain ⟨P, hP, hpos, hneg⟩ := ν.exists_compl_positive_negative
  refine ⟨P, Pᶜ, ⟨hP, ?_⟩, ⟨hP.compl, ?_⟩,
    disjoint_compl_right, union_compl_self P⟩
  · intro A hA hAP
    simpa using (VectorMeasure.restrict_le_restrict_iff 0 ν hP).mp hpos hA hAP
  · intro A hA hAP
    simpa using (VectorMeasure.restrict_le_restrict_iff ν 0 hP.compl).mp hneg hA hAP

theorem hahn_unique {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (P N P' N' : Set α)
    (hP : positiveSet ν P) (hN : negativeSet ν N)
    (_hd : Disjoint P N) (hu : P ∪ N = univ)
    (hP' : positiveSet ν P') (hN' : negativeSet ν N')
    (_hd' : Disjoint P' N') (hu' : P' ∪ N' = univ) :
    (∀ A : Set α, MeasurableSet A → A ⊆ P ∆ P' → ν A = 0) ∧
      partitionVariation ν (P ∆ P') = 0 := by
  have hzero : ∀ A : Set α, MeasurableSet A → A ⊆ P ∆ P' → ν A = 0 := by
    intro A hA hsub
    have hleftP' : A \ P ⊆ P' := by
      intro x hx
      rcases Set.mem_symmDiff.mp (hsub hx.1) with hx' | hx'
      · exact False.elim (hx.2 hx'.1)
      · exact hx'.1
    have hleftN : A \ P ⊆ N := by
      intro x hx
      have hxU : x ∈ P ∪ N := by rw [hu]; trivial
      exact hxU.resolve_left hx.2
    have hrightN' : A ∩ P ⊆ N' := by
      intro x hx
      have hxnot : x ∉ P' := by
        rcases Set.mem_symmDiff.mp (hsub hx.1) with hx' | hx'
        · exact hx'.2
        · exact False.elim (hx'.2 hx.2)
      have hxU : x ∈ P' ∪ N' := by rw [hu']; trivial
      exact hxU.resolve_left hxnot
    have hzleft : ν (A \ P) = 0 :=
      le_antisymm (hN.2 _ (hA.diff hP.1) hleftN)
        (hP'.2 _ (hA.diff hP.1) hleftP')
    have hzright : ν (A ∩ P) = 0 :=
      le_antisymm (hN'.2 _ (hA.inter hP.1) hrightN')
        (hP.2 _ (hA.inter hP.1) Set.inter_subset_right)
    calc
      ν A = ν (A \ P) + ν (A ∩ P) := by
        simpa only [Set.sdiff_union_inter] using
          ν.of_union Set.disjoint_sdiff_inter (hA.diff hP.1) (hA.inter hP.1)
      _ = 0 := by rw [hzleft, hzright, zero_add]
  exact ⟨hzero, (partitionVariation_null_iff ν (P ∆ P')
    (hP.1.symmDiff hP'.1)).mpr hzero⟩

end D11.Ch14.Hahn
