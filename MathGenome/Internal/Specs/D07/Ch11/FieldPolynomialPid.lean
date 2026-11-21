import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.Specs.D07.Ch10.PidDefinition
import MathGenome.Internal.Specs.D07.Ch10.PidUfd
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Field.IsField

/-!
Independent specification for K07.11.field_polynomial_pid,
paper.tex:2363–2386; chapters/M07.11.tex:218–241.

Polynomials are the canonical formal polynomials. The Euclidean relation
uses bottom-valued degree, including degree zero polynomial equal to bottom.
The PID predicate includes nontriviality and the domain condition, even
in the converse, whose coefficient ring is only assumed commutative.
-/

universe u

namespace Specs.D07.Ch11.FieldPolynomialPid

open Polynomial

/-- Chosen Euclidean division data with precisely the degree relation.
Only nonzero divisors require a division identity or remainder decrease. -/
def DegreeEuclideanData : Prop :=
  ∀ (F : Type u) [Field F],
    ∃ d : Ch10.EuclideanDefinition.EuclideanData (Polynomial F),
      d.smaller = (fun p q : Polynomial F => p.degree < q.degree)

/-- Euclideanity in the source's well-founded relation sense. -/
def FieldPolynomialEuclidean : Prop :=
  ∀ (F : Type u) [Field F],
    Ch10.EuclideanDefinition.IsEuclidean (Polynomial F)

/-- Every ideal of the polynomial domain has a single generator. -/
def FieldPolynomialPID : Prop :=
  ∀ (F : Type u) [Field F],
    Ch10.PidDefinition.pidPredicateValue (Polynomial F)

/-- UFD structure and full factorization existence and uniqueness up to
associates and order, using the shared factorization predicate. -/
def FieldPolynomialUFD : Prop :=
  ∀ (F : Type u) [Field F],
    UniqueFactorizationMonoid (Polynomial F) ∧
      Ch10.PidUfd.FactorizationProperty (Polynomial F)

/-- No domain or nontriviality hypothesis on R is added: both must follow
from the domain-sense polynomial PID assumption. The conclusion uses the
given ring operations, rather than an unrelated field structure. -/
def FieldOfPolynomialPID : Prop :=
  ∀ (R : Type u) [CommRing R],
    Ch10.PidDefinition.pidPredicateValue (Polynomial R) → IsField R

end Specs.D07.Ch11.FieldPolynomialPid
