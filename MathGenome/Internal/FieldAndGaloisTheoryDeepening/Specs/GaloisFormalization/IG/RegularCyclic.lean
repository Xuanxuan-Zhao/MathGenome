import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.CyclicBinomialGroup
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.GeometricGaloisGroup
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationData
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationDecomposition
import Mathlib.Data.Nat.Prime.Defs

open Polynomial IntermediateField
open _root_.GaloisFormalization.IG.CyclicBinomial
open Specs.GaloisFormalization.IG.SpecializationData

namespace Specs.GaloisFormalization.IG.RegularCyclic

open _root_.GaloisFormalization.IG.Specs

/-- The splitting field of the binomial is a regular finite Galois realization of
the cyclic group, and the class of the parameter has exact order `n`. -/
def RegularCyclicRealization : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ), 2 ≤ n → IsUnit (n : k) →
    ∀ ζ : k, IsPrimitiveRoot ζ n →
      orderOf (tPowerClass k n) = n ∧
      ∀ (L : Type*) [Field L] [Algebra (RatFunc k) L] [Algebra k L]
        [IsScalarTower k (RatFunc k) L],
        IsSplittingField (RatFunc k) L (binomial k n) →
          FiniteDimensional (RatFunc k) L ∧ IsGalois (RatFunc k) L ∧
            Nonempty ((L ≃ₐ[RatFunc k] L) ≃* Multiplicative (ZMod n)) ∧ isRegularOver k L

/-- In a common algebraic closure, the compositum with the algebraic closure of
constants is the splitting field of the same binomial over the enlarged rational
base. Its group is cyclic of order `n`, and the realization is regular. -/
def GeometricCyclicRealization : Prop :=
  ∀ (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (t : Ω) (_ : Transcendental k t) [Algebra.IsAlgebraic (adjoin k {t}) Ω]
    (n : ℕ), 2 ≤ n → IsUnit (n : k) → ∀ ζ : k, IsPrimitiveRoot ζ n →
    ∀ (L : IntermediateField (adjoin k {t}) Ω),
      IsSplittingField (adjoin k {t}) L (X ^ n - C (AdjoinSimple.gen k t)) →
      let B := _root_.GaloisFormalization.IG.rationalWithConstants t (algebraicClosure k Ω)
      let P := L ⊔ B
      letI : Algebra B P := (inclusion le_sup_right).toAlgebra
      IsSplittingField B P (X ^ n - C (algebraMap (adjoin k {t}) B (AdjoinSimple.gen k t))) ∧
      Nonempty ((P ≃ₐ[B] P) ≃* Multiplicative (ZMod n)) ∧
      isRegularOver k L

/-- All coefficients of the binomial are regular at every finite point. -/
def BinomialRegularAt : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ) (a : k), PolynomialRegularAt a (binomial k n)

/-- Specialization sends the parameter of the binomial to the given point. -/
def BinomialSpecialize : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ) (a : k) (hf : PolynomialRegularAt a (binomial k n)),
    specialize a (binomial k n) hf = X ^ n - C a

/-- Every positive prime gives a separable quadratic fibre whose Galois group is
identified by reduction with the entire generic group. -/
def QuadraticPrimeFullSpecialization : Prop :=
  ∀ {p : ℕ}, p.Prime →
    ∀ (L : Type*) [Field L] [Algebra (RatFunc ℚ) L]
      [IsSplittingField (RatFunc ℚ) L (binomial ℚ 2)]
      (ℓ : Type*) [Field ℓ] [Algebra ℚ ℓ] [IsSplittingField ℚ ℓ (X ^ 2 - C (p : ℚ))],
      (X ^ 2 - C (p : ℚ)).Separable ∧
      Nonempty ((ℓ ≃ₐ[ℚ] ℓ) ≃* Multiplicative (ZMod 2)) ∧
      ∃ (hf : PolynomialRegularAt (p : ℚ) (binomial ℚ 2))
        (i : PointEmbedding (ℓ := ℓ) (p : ℚ) L)
        (d : decompositionGroup i ≃* (ℓ ≃ₐ[ℚ] ℓ)),
        specialize (p : ℚ) (binomial ℚ 2) hf = X ^ 2 - C (p : ℚ) ∧
        MatchesRoots i (binomial ℚ 2) hf ∧
        (∀ (σ : decompositionGroup i) (x : valuationRing i.toRingHom),
          d σ (reduction i.toRingHom x) =
            reduction i.toRingHom
              (_root_.Specs.GaloisFormalization.IG.SpecializationDecomposition.onValuationRing i σ x)) ∧
        decompositionGroup i = ⊤

end Specs.GaloisFormalization.IG.RegularCyclic
