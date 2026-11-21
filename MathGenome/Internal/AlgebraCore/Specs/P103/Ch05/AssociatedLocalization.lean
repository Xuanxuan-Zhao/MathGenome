import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface

/-!
The localization equality of Theorem 5.3 (paper.tex:963–979).
The associated-prime sets use exact element annihilators from the shared
interface. Extension and contraction use the algebra map R → Localization S;
the module on the left has its canonical Localization S scalar action.
No nontriviality or denominator regularity is imposed.
-/
namespace P103.Specs.Ch05.AssociatedLocalization

universe u v
open P103.Specs.Ch05.AssociatedPrimesInterface

/-- The source equality as a set of ideals of the localized ring. -/
def localizationType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (S : Submonoid R),
    associatedPrimesValue (Localization S) (LocalizedModule S M) =
      (fun p : Ideal R => p.map (algebraMap R (Localization S))) ''
        {p | p ∈ associatedPrimesValue R M ∧ Disjoint (S : Set R) (p : Set R)}

/-- The equivalent pointwise statement under contraction of localized primes. -/
def contractionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (S : Submonoid R) (q : Ideal (Localization S)),
    q ∈ associatedPrimesValue (Localization S) (LocalizedModule S M) ↔
      q.comap (algebraMap R (Localization S)) ∈ associatedPrimesValue R M

end P103.Specs.Ch05.AssociatedLocalization
