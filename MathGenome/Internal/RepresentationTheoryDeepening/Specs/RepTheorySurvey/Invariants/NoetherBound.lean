import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous

universe u v w

namespace RepTheorySurvey.Invariants.Specs

open MvPolynomial

/-- In characteristic zero or characteristic greater than the group order, the fixed algebra
of a linear action on a polynomial ring has a finite homogeneous generating set of degrees
at most the group order. The ground field supplies the degree-zero elements. -/
def NoetherBound : Prop :=
  ∀ {k : Type u} {G : Type v} {ι : Type w} [Field k] [Group G] [Fintype G] [Fintype ι]
    (ρ : GroupAlgebraAction k G (MvPolynomial ι k)),
    (∀ g i, (ρ g (X i)).IsHomogeneous 1) →
    (ringChar k = 0 ∨ Fintype.card G < ringChar k) →
    ∃ s : Finset (MvPolynomial ι k),
      (∀ p ∈ s, p ∈ groupFixedSubalgebra ρ ∧
        ∃ d : ℕ, 0 < d ∧ d ≤ Fintype.card G ∧ p.IsHomogeneous d) ∧
      Algebra.adjoin k (s : Set (MvPolynomial ι k)) = groupFixedSubalgebra ρ

end RepTheorySurvey.Invariants.Specs
