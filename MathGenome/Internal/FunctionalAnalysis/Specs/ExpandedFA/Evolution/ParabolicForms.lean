import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.ParabolicGalerkinExistence

/-! The nonautonomous parabolic theorem, paper.tex:15136–15155.
The real Hilbert spaces and the form assumptions are exactly the shared
Galerkin interface. The initial datum fixes the curve also when T = 0.
The constant precedes the form and data, hence depends only on the embedding,
T, M, α, C. Scalar measurability suffices when V is separable. -/
noncomputable section
open MeasureTheory TopologicalSpace
universe u v
namespace ExpandedFA.Evolution.ParabolicFormsSpec
open ParabolicGalerkinSpec

/-- Equality includes the Bochner class, its derivative, and the entire
continuous H-valued representative, including both endpoints. -/
def UniquenessExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M α C : ℝ), FormHypotheses j T a M α C →
    ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
      (z w : WeakSolution j T hT a M f u₀), z = w

/-- Full existence, uniqueness and quantitative estimate under the explicit
strong measurability assumption; no separability or compactness is assumed. -/
def WellposednessExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T) (M α C : ℝ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : BilinearForms V, FormHypotheses j T a M α C →
      ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H),
      ∃ z : WeakSolution j T hT a M f u₀,
        ‖z.curve‖ + ‖z.value‖ + ‖z.derivative‖ ≤ K * (‖u₀‖ + ‖f‖) ∧
        ∀ w : WeakSolution j T hT a M f u₀, w = z

/-- The strong measurability required in the nonseparable theorem follows
from scalar measurability and the simultaneous a.e. bound in a separable V. -/
def SeparableMeasurabilityExpected : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [SeparableSpace V] (T : ℝ) (a : BilinearForms V) (M : ℝ),
    (∀ x y, AEMeasurable (fun t => a t x y) (HilbertTripleSpec.timeMeasureValue T)) →
    (∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T, BoundedAt a M t) →
    ∀ x, AEStronglyMeasurable (fun t => formOperator a M t x)
      (HilbertTripleSpec.timeMeasureValue T)

/-- The source's separable specialization, with no extra operator
measurability hypothesis. The time and zero-space boundary cases are retained. -/
def SeparableWellposednessExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [SeparableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T) (M α C : ℝ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : BilinearForms V, 0 < α →
      (∀ x y, AEMeasurable (fun t => a t x y) (HilbertTripleSpec.timeMeasureValue T)) →
      (∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T, BoundedAt a M t ∧
        ∀ x, α * ‖x‖ ^ 2 - C * ‖j.embedding x‖ ^ 2 ≤ a t x x) →
      ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H),
      ∃ z : WeakSolution j T hT a M f u₀,
        ‖z.curve‖ + ‖z.value‖ + ‖z.derivative‖ ≤ K * (‖u₀‖ + ‖f‖) ∧
        ∀ w : WeakSolution j T hT a M f u₀, w = z
end ExpandedFA.Evolution.ParabolicFormsSpec
