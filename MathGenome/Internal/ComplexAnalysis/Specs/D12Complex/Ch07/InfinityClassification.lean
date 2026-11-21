import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Sphere
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The entire-function part of paper.tex:1782–1812. Polynomiality means
pointwise evaluation of an actual complex polynomial. Positive pole orders are
kept separate from constants, including the zero function. -/
namespace Specs.D12Complex.Ch07.InfinityClassification
open _root_.D12Complex

def removable_iff_constant_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn Set.univ f →
    (RemovableSingularityAtInfinity f ↔ ∃ c : ℂ, ∀ z : ℂ, f z = c)

def pole_iff_polynomial_degree_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn Set.univ f → ∀ m : ℕ, 1 ≤ m →
    (PoleOfOrderAtInfinity f m ↔
      ∃ p : Polynomial ℂ, p.natDegree = m ∧ ∀ z : ℂ, f z = p.eval z)

def nonpolynomial_essential_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn Set.univ f →
    (¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z) →
    EssentialSingularityAtInfinity f

end Specs.D12Complex.Ch07.InfinityClassification
