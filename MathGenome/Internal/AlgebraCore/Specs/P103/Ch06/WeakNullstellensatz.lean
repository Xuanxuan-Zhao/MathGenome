import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for the residue-field assertion of Theorem 6.7
(`paper.tex:1100–1101,1108`). All algebras are commutative and unital.
The base field is arbitrary. Maximal ideals are proper by definition;
no nontriviality hypothesis on the original algebra is needed.
The residue field at a maximal ideal is represented by its quotient.
-/
namespace P103.Specs.Ch06.WeakNullstellensatz

universe u v

/-- Zariski's lemma: a field of finite type over a field is a finite extension. -/
def finite_type_fieldType : Prop :=
  ∀ (k : Type u) (K : Type v) [Field k] [Field K]
    [Algebra k K] [Algebra.FiniteType k K], FiniteDimensional k K

/-- Every maximal quotient of a finite-type algebra is finite-dimensional. -/
def maximal_quotient_finiteType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A), m.IsMaximal → FiniteDimensional k (A ⧸ m)

end P103.Specs.Ch06.WeakNullstellensatz
