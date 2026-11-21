import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.GaussianArithmetic
import MathGenome.Internal.Specs.D07.Ch19.GaussianPrimesTwoSquares

/-! Independent statements for Theorem 4.3 (`nt:D03`), paper.tex:1465–1473
and 1491–1510. The Gaussian ring, integer norm and conjugation are the same
canonical objects as in GaussianArithmetic. PositivePrime means a positive
integer whose natural absolute value is a rational prime. -/

namespace P203Specs.Ch04.GaussianPrimes

open D07.Foundations.IntegerArithmetic

def OneAddIPrime : Prop := Prime (⟨1, 1⟩ : GaussianInt)

def TwoRamifies : Prop :=
  (2 : GaussianInt) = -(⟨0, 1⟩ : GaussianInt) * (⟨1, 1⟩ : GaussianInt) ^ 2

/-- This includes every odd positive rational prime (and also handles 2). -/
def RationalPrimeCriterion : Prop :=
  ∀ p : ℤ, PositivePrime p → (Prime (p : GaussianInt) ↔ p % 4 = 3)

def PrimeOfPrimeNorm : Prop :=
  ∀ z : GaussianInt, PositivePrime z.norm → Prime z

/-- Splitting at every rational prime congruent to 1 modulo 4, with an actual
conjugate product, both norms, primality of both factors, and nonassociation. -/
def ConjugateFactorization : Prop :=
  ∀ p : ℤ, PositivePrime p → p % 4 = 1 →
    ∃ π : GaussianInt, π.norm = p ∧ (star π).norm = p ∧
      (p : GaussianInt) = π * star π ∧ Prime π ∧ Prime (star π) ∧
      ¬ Associated π (star π)

/-- Exhaustion in both directions, with all unit multiples and signed
coordinates included. -/
def GaussianPrimeClassification : Prop :=
  ∀ z : GaussianInt, Prime z ↔
    Associated z (⟨1, 1⟩ : GaussianInt) ∨
    (∃ p : ℤ, PositivePrime p ∧ p % 4 = 3 ∧ Associated z (p : GaussianInt)) ∨
    (PositivePrime z.norm ∧ z.norm % 4 = 1)

end P203Specs.Ch04.GaussianPrimes
