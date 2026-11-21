import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.ConvexFunctionRepresentation
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The full interval-domain statement of paper.tex:6521–6567.
The ambient function space has its product topology (pointwise convergence).
The canonical hinge and normalization are shared with the representation theorem;
in particular the hinge at 1 is discontinuous as a function of x. -/
namespace ExpandedFA.Supplements.ConvexFunctionExtremesSpec

open Set MeasureTheory
open scoped ENNReal
open ConvexFunctionRepresentationSpec

abbrev FunctionSpace := UnitInterval → ℝ

def normalizedSet : Set FunctionSpace := {f | IntervalNormalized f}

noncomputable def hingeFunction (r : UnitInterval) : FunctionSpace := fun x => hinge r (x : ℝ)

noncomputable def probabilityMap (μ : ProbabilityMeasure UnitInterval) : FunctionSpace :=
  fun x => mixture (μ : Measure UnitInterval) (x : ℝ)

def CompactConvex : Prop := IsCompact normalizedSet ∧ Convex ℝ normalizedSet

def Classification : Prop :=
  ExpandedFA.P1.C24FacesSpec.extremePoints normalizedSet = Set.range hingeFunction

def Representation : Prop :=
  ∀ f ∈ normalizedSet, ∃! μ : Measure UnitInterval, IntervalRepresents μ f

/-- The actual integral map is continuous, bijective onto the normalized set,
and preserves every probability convex combination. -/
def AffineRepresentation : Prop :=
  Continuous probabilityMap ∧ Function.Injective probabilityMap ∧
  Set.range probabilityMap = normalizedSet ∧
  ∀ (μ ν : Measure UnitInterval) (a b : ℝ≥0∞),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν → a + b = 1 →
    ∀ x : UnitInterval,
      mixture (a • μ + b • ν) (x : ℝ) =
        a.toReal * mixture μ (x : ℝ) + b.toReal * mixture ν (x : ℝ)

end ExpandedFA.Supplements.ConvexFunctionExtremesSpec
