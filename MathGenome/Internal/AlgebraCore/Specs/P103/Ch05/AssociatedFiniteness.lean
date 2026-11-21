import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface

/-!
The associated-prime assertions of Theorem 5.4 (paper.tex:984–988).
`associatedPrimesValue` is the source's set of prime ideals that are exact
annihilators of elements. `Module.Finite` means finitely generated, and
`Nontrivial M` expresses that the module is nonzero. No nonzero assumption
is imposed on the ring. The support assertions are allocated separately.
-/
namespace P103.Specs.Ch05.AssociatedFiniteness

open P103.Specs.Ch05.AssociatedPrimesInterface
universe u v

def associatedPrimes_finiteType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    (associatedPrimesValue R M).Finite

def associatedPrimes_nonempty_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    (associatedPrimesValue R M).Nonempty ↔ Nontrivial M

/-- The zero-module assertion holds without either finiteness hypothesis. -/
def associatedPrimes_eq_emptyType : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M],
    associatedPrimesValue R M = ∅

end P103.Specs.Ch05.AssociatedFiniteness
