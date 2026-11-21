import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FiniteFieldStandardFactors
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! ET-20, paper.tex:2062–2077. The algebra on the fourfold product is
componentwise, with the diagonal structural maps. Residue fields below are
those of actual primes, rather than a count of algebra homomorphisms. -/
namespace Specs.AdvCommAlg.Etale.CompositeNotStandard

open Polynomial
open Specs.AdvCommAlg.Etale.StandardAndPointwise
open Specs.AdvCommAlg.Etale.FiniteFieldStandardFactors

/-- There is exactly one monic irreducible quadratic over the prime field. -/
def uniqueQuadratic : Prop :=
  ∀ p : (ZMod 2)[X], p.Monic → p.natDegree = 2 → Irreducible p → p = quadratic

/-- In fact the obstruction holds for every localized one-variable quotient,
without requiring monicity or a unit derivative. -/
def localizedResidueObstruction : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
    Fintype.card K = 4 → ∀ f g : (ZMod 2)[X],
    ∀ p q : PrimeSpectrum (LocalizedQuotient f g),
    Nonempty (p.asIdeal.ResidueField ≃ₐ[ZMod 2] K) →
    Nonempty (q.asIdeal.ResidueField ≃ₐ[ZMod 2] K) → p = q

/-- Four distinct primes of the product have the specified residue field. -/
def fourResiduePrimes : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K], Fintype.card K = 4 →
    ∃ p : Fin 4 → PrimeSpectrum (Fin 4 → K), Function.Injective p ∧
      ∀ i, Nonempty ((p i).asIdeal.ResidueField ≃ₐ[ZMod 2] K)

/-- No localized one-variable quotient is the fourfold product over F₂. -/
def noSingleVariablePresentation : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K], Fintype.card K = 4 →
    ∀ f g : (ZMod 2)[X], ¬ Nonempty ((Fin 4 → K) ≃ₐ[ZMod 2] LocalizedQuotient f g)

/-- The two standard maps compose to an étale map that is not standard in
ET-06's monic localized one-variable sense. -/
def compositeExample : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K], Fintype.card K = 4 →
    standardEtaleValue (ZMod 2) K ∧ standardEtaleValue K (Fin 4 → K) ∧
    etaleValue (ZMod 2) (Fin 4 → K) ∧ ¬ standardEtaleValue (ZMod 2) (Fin 4 → K)

end Specs.AdvCommAlg.Etale.CompositeNotStandard
