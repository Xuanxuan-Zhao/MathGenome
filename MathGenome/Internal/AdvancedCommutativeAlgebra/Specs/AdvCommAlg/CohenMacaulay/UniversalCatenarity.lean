import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.PrimeChains
import Mathlib.RingTheory.FiniteType

/-! Independent statements for the universal catenarity consequence of CM-15
(paper.tex:3768–3769,3813–3817). Catenarity uses the prime-interval
convention of CM-07. The finite type algebra need not be Cohen–Macaulay.
The empty set of polynomial variables and zero rings are included. -/
universe u v
namespace AdvCommAlg.CohenMacaulay.Specs

/-- Finite polynomial extensions of a Noetherian CM ring are catenary. -/
def mvPolynomial_catenaryType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ n : ℕ,
      CatenaryValue (MvPolynomial (Fin n) R)

/-- Surjective homomorphisms preserve catenarity, without a CM condition
on the target or a Noetherian condition on either ring. -/
def catenary_of_surjectiveType : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S), Function.Surjective f → CatenaryValue R → CatenaryValue S

/-- In particular every ideal quotient of a catenary ring is catenary. -/
def quotient_catenaryType : Prop :=
  ∀ (R : Type u) [CommRing R], CatenaryValue R →
    ∀ I : Ideal R, CatenaryValue (R ⧸ I)

/-- Universal catenarity: every finitely generated commutative algebra over
a Noetherian Cohen–Macaulay ring is catenary. -/
def universally_catenaryType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ (B : Type v) [CommRing B] [Algebra R B]
      [Algebra.FiniteType R B], CatenaryValue B

end AdvCommAlg.CohenMacaulay.Specs
