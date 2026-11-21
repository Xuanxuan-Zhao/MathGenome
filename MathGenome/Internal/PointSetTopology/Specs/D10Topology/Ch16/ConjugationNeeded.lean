import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.SupNormAlgebras
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.ContinuousMap.Polynomial

/-! The unit circle has its usual subspace topology. The algebra below is the
range of evaluation at the coordinate, so it uses ordinary polynomials in z
alone. The closure is the uniform closure fixed in chapter 13. -/
noncomputable section
open scoped ComplexConjugate
namespace Specs.D10Topology.Ch16.ConjugationNeeded

open Polynomial

/-- The coordinate function on the usual complex unit circle. -/
def coordinate : C(Circle, ℂ) := ⟨fun z => z, continuous_subtype_val⟩
def coordinateType := C(Circle, ℂ)

/-- Complex conjugation of the coordinate. -/
def conjugateCoordinate : C(Circle, ℂ) := star coordinate

/-- Restriction of an ordinary complex polynomial to the unit circle. -/
def polynomialRestriction (p : ℂ[X]) : C(Circle, ℂ) := aeval coordinate p
def polynomialRestrictionType := ℂ[X] → C(Circle, ℂ)

/-- The unital complex algebra of ordinary polynomial restrictions. -/
def polynomialAlgebra : Subalgebra ℂ C(Circle, ℂ) := (aeval coordinate).range
def polynomialAlgebraType := Subalgebra ℂ C(Circle, ℂ)

def restriction_apply : Prop :=
  ∀ (p : ℂ[X]) (z : Circle), polynomialRestriction p z = p.eval (z : ℂ)

def conjugate_apply : Prop :=
  ∀ z : Circle, conjugateCoordinate z = conj (z : ℂ)

def mem_polynomialAlgebra_iff : Prop :=
  ∀ f : C(Circle, ℂ), f ∈ polynomialAlgebra ↔ ∃ p : ℂ[X], polynomialRestriction p = f

def contains_constants : Prop :=
  ∀ c : ℂ, ContinuousMap.const Circle c ∈ polynomialAlgebra

def separates_points : Prop :=
  SupNormAlgebras.SeparatesPoints (polynomialAlgebra : Set C(Circle, ℂ))

/-- A quantitative obstruction, stronger than failure of approximation. -/
def conjugate_distance_ge_one : Prop :=
  ∀ p : ℂ[X], 1 ≤ SupNormAlgebras.supNorm (conjugateCoordinate - polynomialRestriction p)

def conjugate_not_uniformly_approximable : Prop :=
  ¬ (∀ ε : ℝ, 0 < ε → ∃ p : ℂ[X],
    ∀ z : Circle, ‖conj (z : ℂ) - p.eval (z : ℂ)‖ < ε)

def conjugate_not_mem_uniformClosure : Prop :=
  conjugateCoordinate ∉ SupNormAlgebras.uniformClosure (polynomialAlgebra : Set C(Circle, ℂ))

def not_uniformly_dense : Prop :=
  SupNormAlgebras.uniformClosure (polynomialAlgebra : Set C(Circle, ℂ)) ≠ Set.univ

end Specs.D10Topology.Ch16.ConjugationNeeded
