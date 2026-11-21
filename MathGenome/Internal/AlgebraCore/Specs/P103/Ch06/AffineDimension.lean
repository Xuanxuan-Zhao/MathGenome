import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Algebra

/-! Independent statements for Theorem 6.6, paper.tex:1089–1097.
The field is arbitrary. Dimension is the supremum of strict prime-chain
lengths, with values in `WithBot ℕ∞`. The transcendence degree is a cardinal;
`domain_finite_ranksType` asserts finiteness before the explicit comparison
through `Cardinal.toENat`. In particular the value zero is retained.
The minimal-prime statements impose neither reducedness nor equidimensionality.
-/
namespace P103.Specs.Ch06.AffineDimension

universe u v

/-- The two ranks agree as finite natural numbers. -/
def domain_finite_ranksType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A],
    ∃ d : ℕ, ringKrullDim A = (d : WithBot ℕ∞) ∧
      Algebra.trdeg k (FractionRing A) = (d : Cardinal)

/-- Krull dimension equals the transcendence degree of the fraction field. -/
def domain_dimensionType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A],
    ringKrullDim A = ((Algebra.trdeg k (FractionRing A)).toENat : WithBot ℕ∞)

def minimalPrimes_finite_nonemptyType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A],
    (minimalPrimes A).Finite ∧ (minimalPrimes A).Nonempty

/-- The component dimensions form a finite nonempty set whose greatest member
is the dimension of A. `IsGreatest` includes attainment by a minimal prime. -/
def dimension_maximal_componentsType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A],
    let dims := (fun P : Ideal A => ringKrullDim (A ⧸ P)) '' minimalPrimes A
    dims.Finite ∧ dims.Nonempty ∧ IsGreatest dims (ringKrullDim A)

end P103.Specs.Ch06.AffineDimension
