import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Algebra.Pi

/-! ET-20, the two individual standard presentations. The product algebra
has the diagonal structural map and componentwise operations. -/
namespace Specs.AdvCommAlg.Etale.FiniteFieldStandardFactors

open Polynomial
open Specs.AdvCommAlg.Etale.StandardAndPointwise

/-- The specified polynomial over the prime field. -/
noncomputable def quadratic : (ZMod 2)[X] := X ^ 2 + X + 1

/-- One distinct linear factor for every element of the field. -/
noncomputable def splitPolynomial (K : Type*) [Field K] [Fintype K] : K[X] :=
  ∏ a : K, (X - C a)

def quadraticFacts : Prop :=
  quadratic.Monic ∧ quadratic.natDegree = 2 ∧ Irreducible quadratic ∧
    quadratic.derivative = 1

/-- Includes the specified quotient, its unit derivative, and its presentation
with denominator 1 as a standard étale algebra. -/
def firstPresentation : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
    Fintype.card K = 4 →
    Nonempty (AdjoinRoot quadratic ≃ₐ[ZMod 2] K) ∧
    IsUnit (AdjoinRoot.mk quadratic quadratic.derivative) ∧
    Nonempty (K ≃ₐ[ZMod 2] LocalizedQuotient quadratic 1) ∧
    standardEtaleValue (ZMod 2) K

/-- Distinct linear factors are comaximal and their product has degree four.
At each component the derivative is a nonzero element of the field. -/
def splitFacts : Prop :=
  ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 4 →
    (splitPolynomial K).Monic ∧ (splitPolynomial K).natDegree = 4 ∧
    (∀ a b : K, a ≠ b →
      IsCoprime (Ideal.span ({X - C a} : Set K[X]))
        (Ideal.span ({X - C b} : Set K[X]))) ∧
    (∀ a : K, IsUnit ((splitPolynomial K).derivative.eval a))

/-- The CRT equivalence is evaluation at each of the four roots. The derivative
is a unit in the quotient, and reindexing the factors gives the usual K^4. -/
def secondPresentation : Prop :=
  ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 4 →
    (∃ e : AdjoinRoot (splitPolynomial K) ≃ₐ[K] (K → K),
      ∀ (p : K[X]) (a : K), e (AdjoinRoot.mk (splitPolynomial K) p) a = p.eval a) ∧
    IsUnit (AdjoinRoot.mk (splitPolynomial K) (splitPolynomial K).derivative) ∧
    Nonempty ((Fin 4 → K) ≃ₐ[K] LocalizedQuotient (splitPolynomial K) 1) ∧
    standardEtaleValue K (Fin 4 → K)

end Specs.AdvCommAlg.Etale.FiniteFieldStandardFactors
