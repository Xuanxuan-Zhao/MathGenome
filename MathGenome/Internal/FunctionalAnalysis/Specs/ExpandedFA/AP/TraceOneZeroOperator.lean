import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.SummableTensorFlattening
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.AdjacentTensorDifferences

/-! The closing rank-one series in paper.tex:12889–12908. Indices start at
zero, so `u D 0` is the manuscript's first tensor. The original closed span,
continuous real dual, and algebraic tensor product are retained. -/
noncomputable section
namespace ExpandedFA.AP.TraceOneZeroOperator.Spec
open EnfloSpace.Spec AlgebraicRankOneTensorsSpec SummableTensorFlatteningSpec
open Filter

/-- Normalized diagonal functional on bounded endomorphisms. -/
def tau (D : IncidenceData) (m : ℕ) (T : X D →L[ℝ] X D) : ℝ :=
  ((k D m : ℝ) * t D m)⁻¹ * ∑ e : Symbol D m,
    EnfloCoordinates.Spec.coordinate D ⟨m, e⟩ (T (generatorX D m e))

def TauType := ∀ (D : IncidenceData) (_m : ℕ), (X D →L[ℝ] X D) → ℝ
def TauValue : TauType := tau

def TauBound : Prop := ∀ D m (T : X D →L[ℝ] X D), |tau D m T| ≤ ‖T‖

def TauFiniteRankLimit : Prop := ∀ D (T : X D →L[ℝ] X D),
  FiniteDimensional ℝ (LinearMap.range T.toLinearMap) →
    Tendsto (fun m => tau D m T) atTop (nhds 0)

/-- The actual initial-plus-differences flattening, with its representations,
absolute cost, trace one, and zero operator sum. The pointwise series identity
is included for direct use in the trace obstruction. -/
def TraceOneZeroSeries : Prop := ∀ D : IncidenceData,
  ∃ l : ℕ → List ((X D →L[ℝ] ℝ) × X D),
    tensorSum (l 0) = EnfloCoordinates.Spec.u D 0 ∧
    (∀ m, tensorSum (l (m + 1)) =
      EnfloCoordinates.Spec.u D (m + 1) - EnfloCoordinates.Spec.u D m) ∧
    Summable (fun m => cost (l m)) ∧
    Summable (fun j => ‖(flattenedPair l j).1‖ * ‖(flattenedPair l j).2‖) ∧
    HasSum (fun j => (flattenedPair l j).1 (flattenedPair l j).2) 1 ∧
    HasSum (fun j => (flattenedPair l j).1.smulRight (flattenedPair l j).2) 0 ∧
    (∀ x : X D, HasSum (fun j => (flattenedPair l j).1 x • (flattenedPair l j).2) 0)

/-- Operator-norm convergence is stronger than the pointwise limit required
by the source and makes its limiting operator unambiguous. -/
def OperatorLimit : Prop := ∀ D,
  Tendsto (fun m => operator (EnfloCoordinates.Spec.u D m)) atTop (nhds 0)
end ExpandedFA.AP.TraceOneZeroOperator.Spec
