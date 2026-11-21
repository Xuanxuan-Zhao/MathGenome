import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.CylinderFramework

/-! Independent specification of paper.tex, Lemma `countable-cylinder-reduction`.
The Pi measurable structure used here is the cylinder sigma-algebra, as established
by the upstream `CylinderSigmaEqPi` interface. No completion is taken.
-/

open MeasureTheory

namespace ProbabilityFoundations.Ch05.CountableCylinderReduction

open CylinderFramework

universe u v

/-- Projection from a coordinate subfamily onto an original finite support. -/
def subfamilyProjection {I : Type u} (S : I → Type v) (J : Set I)
    (F : Finset I) (hF : (↑F : Set I) ⊆ J) :
    ProductSpace (fun i : J => S i) → FiniteProduct S F :=
  fun x i => x ⟨i, hF i.property⟩

/-- This includes finite and empty subfamilies and all of their finite laws. -/
def HasCountableExtensions {I : Type u} (S : I → Type v)
    [∀ i, MeasurableSpace (S i)] (μ : FiniteLaws S) : Prop :=
  ∀ J : Set I, J.Countable →
    ∃ ν : Measure (ProductSpace (fun i : J => S i)),
      IsProbabilityMeasure ν ∧
      ∀ (F : Finset I) (hF : (↑F : Set I) ⊆ J),
        Measure.map (subfamilyProjection S J F hF) ν = μ F

end ProbabilityFoundations.Ch05.CountableCylinderReduction

namespace Specs.ProbabilityFoundations.Ch05.CountableCylinderReduction

open _root_.ProbabilityFoundations.Ch05.CylinderFramework
open _root_.ProbabilityFoundations.Ch05.CountableCylinderReduction

universe u v

/-- Existence and uniqueness on the product/cylinder sigma-algebra for arbitrary I. -/
def ReductionTheorem : Prop :=
  ∀ {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    [∀ i, Nonempty (S i)] (μ : FiniteLaws S),
    IsProbabilityFamily S μ → Consistent S μ → HasCountableExtensions S μ →
    ∃! ν : Measure (ProductSpace S),
      IsProbabilityMeasure ν ∧
      ∀ F : Finset I, Measure.map (finiteProjection S F) ν = μ F

end Specs.ProbabilityFoundations.Ch05.CountableCylinderReduction
