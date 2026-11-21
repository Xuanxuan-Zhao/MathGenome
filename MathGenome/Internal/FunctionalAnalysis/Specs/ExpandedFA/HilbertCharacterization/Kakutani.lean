import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Parallelogram
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Independent specification of paper.tex:9266–9290 (fa2:p2:kakutani).
Dimension is cardinal dimension, so infinite-dimensional and incomplete real
normed spaces are included. Projections have exactly norm one. -/
noncomputable section
namespace ExpandedFA.HilbertCharacterization.Kakutani
universe u

/-- The inner product uses the original norm and scalar multiplication. -/
def HasCompatibleInnerProduct (X : Type u) [NormedAddCommGroup X]
    [n : NormedSpace ℝ X] : Prop :=
  ∃ p : InnerProductSpace ℝ X, p.toNormedSpace = n

/-- An ambient-valued bounded linear idempotent of exact norm one onto every plane. -/
def NormOnePlaneProjections (X : Type u) [NormedAddCommGroup X]
    [NormedSpace ℝ X] : Prop :=
  ∀ L : Submodule ℝ X, Module.finrank ℝ L = 2 →
    ∃ P : X →L[ℝ] X, P.comp P = P ∧ LinearMap.range P.toLinearMap = L ∧ ‖P‖ = 1

namespace Spec

def Characterization : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    (3 : Cardinal) ≤ Module.rank ℝ X →
    (HasCompatibleInnerProduct X ↔ NormOnePlaneProjections X)

/-- A Hilbert structure is a compatible inner product and completeness of its
induced metric. The normed additive group is unchanged by this construction. -/
def CompleteConclusion : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [n : NormedSpace ℝ X] [CompleteSpace X],
    (3 : Cardinal) ≤ Module.rank ℝ X → NormOnePlaneProjections X →
    ∃ p : InnerProductSpace ℝ X, p.toNormedSpace = n ∧ CompleteSpace X

/-- In dimension two the only plane is the whole space and its identity has
norm one, regardless of the shape of the unit ball. -/
def TwoDimensionalIdentity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    Module.finrank ℝ X = 2 →
    ∀ L : Submodule ℝ X, Module.finrank ℝ L = 2 →
      L = ⊤ ∧ (ContinuousLinearMap.id ℝ X).comp (ContinuousLinearMap.id ℝ X) =
        ContinuousLinearMap.id ℝ X ∧
      LinearMap.range (ContinuousLinearMap.id ℝ X).toLinearMap = L ∧
      ‖ContinuousLinearMap.id ℝ X‖ = 1

/-- The real plane with the maximum norm is an explicit obstruction. -/
def TwoDimensionalObstruction : Prop :=
  Module.finrank ℝ (ℝ × ℝ) = 2 ∧ NormOnePlaneProjections (ℝ × ℝ) ∧
    ¬ HasCompatibleInnerProduct (ℝ × ℝ)

end Spec
end ExpandedFA.HilbertCharacterization.Kakutani
