import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! The selector is a set of real numbers, meeting each rational-difference
class in [0,1] exactly once. Completed measurability is tested in the canonical
one-dimensional Euclidean space using its coordinate identification with ℝ.
The coordinate inverse image is the corresponding subset of `Point 1`.
No Borel measurability assumption is substituted for completed measurability. -/

open Set MeasureTheory

namespace D11.Ch03.Vitali

/-- Rational-difference equivalence on real numbers. -/
def RationalEquivalent (x y : ℝ) : Prop := ∃ q : ℚ, x - y = (q : ℝ)

/-- Exactly one representative from each class that meets [0,1]. -/
def IsSelector (V : Set ℝ) : Prop :=
  V ⊆ Icc 0 1 ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∃! v, v ∈ V ∧ RationalEquivalent x v

/-- Transport a real set to canonical Euclidean one-space by its only coordinate. -/
def inOneSpace (V : Set ℝ) : Set (Point 1) := {p | p 0 ∈ V}

end D11.Ch03.Vitali

namespace Specs.D11.Ch03.Vitali

open _root_.D11.Ch03.Vitali

def selector_exists : Prop := ∃ V : Set ℝ, IsSelector V

def selector_nonmeasurable : Prop := ∀ V : Set ℝ, IsSelector V →
  ¬ MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1] (inOneSpace V)

end Specs.D11.Ch03.Vitali
