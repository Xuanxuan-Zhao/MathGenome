import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! Independent specifications for the definition and Theorem 4.1 in §4.1 of paper.tex.
The subtype carries the trace of the ambient Borel sigma-algebra. `MeasurableEquiv`
is a bijection with measurable forward and inverse maps, as required by the source.
No topology is imposed on the given measurable space. -/
namespace ProbabilityFoundations.Ch04.Specs

open Set MeasureTheory TopologicalSpace

universe u v

/-- The source definition, with a complete separable metric ambient space. -/
def StandardBorelValue (T : Type u) [MeasurableSpace T] : Prop :=
  ∃ (M : Type u) (d : MetricSpace M),
    @CompleteSpace M d.toUniformSpace ∧ @SeparableSpace M d.toUniformSpace.toTopologicalSpace ∧
    ∃ B : Set M, @MeasurableSet M (@borel M d.toUniformSpace.toTopologicalSpace) B ∧
      Nonempty (@MeasurableEquiv T B ‹MeasurableSpace T›
        (@MeasurableSpace.comap B M Subtype.val (@borel M d.toUniformSpace.toTopologicalSpace)))

def StandardBorelType := (T : Type u) → [MeasurableSpace T] → Prop

def LibraryBridge : Prop :=
  ∀ (T : Type u) [MeasurableSpace T], StandardBorelValue T ↔ StandardBorelSpace T

def RealCoding : Prop :=
  ∀ (T : Type u) [MeasurableSpace T], StandardBorelValue T →
    ∃ B : Set ℝ, MeasurableSet B ∧ Nonempty (T ≃ᵐ B)

def CountableGeneratingPiSystem : Prop :=
  ∀ (T : Type u) [m : MeasurableSpace T], StandardBorelValue T →
    ∃ C : Set (Set T), C.Countable ∧ IsPiSystem C ∧
      (∀ A ∈ C, ∀ B ∈ C, A ∩ B ∈ C) ∧ univ ∈ C ∧
      MeasurableSpace.generateFrom C = m

def FiniteProducts : Prop :=
  ∀ (ι : Type v) [Finite ι] (T : ι → Type u) [∀ i, MeasurableSpace (T i)],
    (∀ i, StandardBorelValue (T i)) → StandardBorelValue (∀ i, T i)

end ProbabilityFoundations.Ch04.Specs
