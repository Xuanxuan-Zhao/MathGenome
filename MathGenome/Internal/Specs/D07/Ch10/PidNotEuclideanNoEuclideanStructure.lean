import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.Specs.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm

/-! Independent statements for the non-Euclidean assertion in
paper.tex:2122–2140. The ring is the original complex subring ℤ[omega],
with its inherited operations; the Euclidean predicate allows every
well-founded remainder relation, without a norm compatibility axiom. -/

universe u

namespace D07.Ch10.PidNotEuclideanNoEuclideanStructure.Specs

/-- A nonzero nonunit which divides every element after subtracting zero
or a unit, as in the source's universal side-divisor criterion. -/
def UniversalSideDivisor {A : Type u} [CommRing A] (a : A) : Prop :=
  a ≠ 0 ∧ ¬ IsUnit a ∧
    ∀ x : A, ∃ ε : A, (ε = 0 ∨ IsUnit ε) ∧ a ∣ x - ε

/-- Minimal nonzero nonunits in a Euclidean nonfield yield side divisors.
Nonfieldness is expressed by the existence of a nonzero nonunit. -/
def EuclideanHasUniversalSideDivisor : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A],
    _root_.Specs.D07.Ch10.EuclideanDefinition.IsEuclidean A →
    (∃ a : A, a ≠ 0 ∧ ¬ IsUnit a) →
    ∃ a : A, UniversalSideDivisor a

def NoUniversalSideDivisor : Prop :=
  ¬ ∃ a : PidNotEuclideanQuadraticIntegerNorm.R, UniversalSideDivisor a

def NotEuclidean : Prop :=
  ¬ _root_.Specs.D07.Ch10.EuclideanDefinition.IsEuclidean
    PidNotEuclideanQuadraticIntegerNorm.R

end D07.Ch10.PidNotEuclideanNoEuclideanStructure.Specs
