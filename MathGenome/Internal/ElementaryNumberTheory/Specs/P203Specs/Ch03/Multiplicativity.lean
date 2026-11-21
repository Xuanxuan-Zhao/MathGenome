import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Convolution
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.FactorizationValuations

/-! The algebraic assertions of paper.tex, Theorem 3.2 (nt:C02),
lines 899–908, with the positive-input and valuation conventions of Chapters 1 and 3.
The analytic Euler product assertion is allocated separately to C02b. -/
namespace P203Specs.Multiplicativity

/-- Multiplicativity on precisely the source's positive domain. -/
def IsMultiplicative {R : Type*} [CommRing R] (f : PositiveFunction R) : Prop :=
  f 1 = 1 ∧ ∀ a b : ℕ+, Nat.Coprime (a : ℕ) (b : ℕ) → f (a * b) = f a * f b

/-- The canonical zero extension imposes no additional multiplicativity assumption. -/
def MultiplicativityBridge : Prop :=
  ∀ (R : Type*) [CommRing R] (f : PositiveFunction R),
    IsMultiplicative f ↔ ArithmeticFunction.IsMultiplicative (zeroExtend f)

/-- Reconstruction using the same canonical integer valuation as Chapter 1.
The zero extension only avoids notation for positive prime powers; all arguments
in the product are positive. For n=1 the product is empty. -/
def PrimePowerFormula : Prop :=
  ∀ (R : Type*) [CommRing R] (f : PositiveFunction R), IsMultiplicative f →
    ∀ n : ℕ+,
      f n = ∏ p ∈ (n : ℕ).primeFactors,
        zeroExtend f (p ^ (Ch01.primeValuation p (n : ℤ)).toNat)

/-- Only the values c(p,j) with p prime and j positive are prescribed.
Values of this total indexing function elsewhere have no constraints or role. -/
def PrimePowerExtension : Prop :=
  ∀ (R : Type*) [CommRing R] (c : ℕ → ℕ → R),
    ∃! f : PositiveFunction R, IsMultiplicative f ∧
      ∀ p : ℕ, p.Prime → ∀ j : ℕ, 0 < j → zeroExtend f (p ^ j) = c p j

def ConvolutionClosure : Prop :=
  ∀ (R : Type*) [CommRing R] (f g : PositiveFunction R),
    IsMultiplicative f → IsMultiplicative g →
      IsMultiplicative (positiveConvolution f g)

/-- The unique two-sided inverse in C01's convolution ring exists and is
multiplicative. There is no pointwise inverse operation in this statement. -/
def InverseClosure : Prop :=
  ∀ (R : Type*) [CommRing R] (f : PositiveFunction R), IsMultiplicative f →
    ∃! g : PositiveFunction R, IsMultiplicative g ∧
      positiveConvolution f g = delta R ∧ positiveConvolution g f = delta R

end P203Specs.Multiplicativity
