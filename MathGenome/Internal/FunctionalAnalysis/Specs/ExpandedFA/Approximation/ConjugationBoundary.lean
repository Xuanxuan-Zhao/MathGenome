import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.MeasureTheory.Integral.CircleAverage

/-! Independent statements for the example at paper.tex:6513--6519.
The domain is the entire complex unit circle. The algebra consists of restrictions
of ordinary complex polynomials in `z`, with no negative powers or conjugates.
The continuous-map norm on this compact domain is the uniform norm.
`Real.circleAverage` is integration against normalized angular measure dθ/(2π),
not the complex contour integral against dz.
-/

namespace Specs.ExpandedFA.Approximation.ConjugationBoundary

abbrev UnitCircle := ↥(Metric.sphere (0 : ℂ) 1)

noncomputable abbrev polynomialAlgebra : Subalgebra ℂ C(UnitCircle, ℂ) :=
  polynomialFunctions (Metric.sphere (0 : ℂ) 1)

/-- Complex conjugation restricted to the unit circle. -/
noncomputable def conjugation : C(UnitCircle, ℂ) :=
  ⟨fun z => star (z : ℂ), continuous_star.comp continuous_subtype_val⟩

def ContainsConstants : Prop :=
  ∀ c : ℂ, ContinuousMap.const UnitCircle c ∈ polynomialAlgebra

def SeparatesPoints : Prop := polynomialAlgebra.SeparatesPoints

def PolynomialMeanZero : Prop :=
  ∀ p : Polynomial ℂ, Real.circleAverage (fun z => z * p.eval z) 0 1 = 0

def ConjugationMeanOne : Prop :=
  Real.circleAverage (fun z : ℂ => z * star z) 0 1 = 1

/-- In fact the distance of conjugation from every polynomial is at least one. -/
def UniformErrorLowerBound : Prop :=
  ∀ p : Polynomial ℂ,
    1 ≤ ‖p.toContinuousMapOn (Metric.sphere (0 : ℂ) 1) - conjugation‖

def NonApproximation : Prop :=
  conjugation ∉ closure (polynomialAlgebra : Set C(UnitCircle, ℂ))

def NotDense : Prop :=
  ¬ Dense (polynomialAlgebra : Set C(UnitCircle, ℂ))

def NotConjugationClosed : Prop :=
  ¬ ∀ f ∈ polynomialAlgebra, star f ∈ polynomialAlgebra

end Specs.ExpandedFA.Approximation.ConjugationBoundary
