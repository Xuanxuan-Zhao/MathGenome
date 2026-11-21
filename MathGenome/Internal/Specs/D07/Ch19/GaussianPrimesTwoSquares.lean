import MathGenome.Internal.Specs.D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion

/-!
Independent statements for K07.19.gaussian_primes_two_squares,
paper.tex:5680–5731. Gaussian integers use their canonical integer-coordinate
model and integer-valued squared norm. `Associated` means equality up to a
unit. In the third family this qualification is unnecessary because units
preserve the norm; all signed coordinates, including conjugates, are allowed.
-/

namespace Specs.D07.Ch19.GaussianPrimesTwoSquares

open D07.Foundations.IntegerArithmetic

def PrimeTwoSquareCriterion : Prop :=
  ∀ p : ℤ, PositivePrime p →
    ((∃ a b : ℤ, p = a ^ 2 + b ^ 2) ↔ p = 2 ∨ p % 4 = 1)

def PrimeOfPrimeNorm : Prop :=
  ∀ z : GaussianInt, PositivePrime z.norm → Prime z

def OneAddIPrime : Prop := Prime (⟨1, 1⟩ : GaussianInt)

def TwoRamifies : Prop :=
  (2 : GaussianInt) = -(⟨0, 1⟩ : GaussianInt) * (⟨1, 1⟩ : GaussianInt) ^ 2

def NormTwoAssociates : Prop :=
  ∀ z : GaussianInt, z.norm = 2 ↔ Associated z (⟨1, 1⟩ : GaussianInt)

def RationalPrimeCriterion : Prop :=
  ∀ q : ℤ, PositivePrime q → (Prime (q : GaussianInt) ↔ q % 4 = 3)

/-- Exhaustion and primality of each family, including the ramified prime. -/
def GaussianPrimeClassification : Prop :=
  ∀ z : GaussianInt, Prime z ↔
    Associated z (⟨1, 1⟩ : GaussianInt) ∨
    (∃ q : ℤ, PositivePrime q ∧ q % 4 = 3 ∧ Associated z (q : GaussianInt)) ∨
    (PositivePrime z.norm ∧ z.norm % 4 = 1)

/-- The same exhaustive list expressed in terms of irreducibility. -/
def GaussianIrreducibleClassification : Prop :=
  ∀ z : GaussianInt, Irreducible z ↔
    Associated z (⟨1, 1⟩ : GaussianInt) ∨
    (∃ q : ℤ, PositivePrime q ∧ q % 4 = 3 ∧ Associated z (q : GaussianInt)) ∨
    (PositivePrime z.norm ∧ z.norm % 4 = 1)

end Specs.D07.Ch19.GaussianPrimesTwoSquares
