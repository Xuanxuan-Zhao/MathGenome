import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
Independent specifications for paper.tex, Proposition p204:W11.
The derivative is Mathlib's canonical formal derivative; coefficients and
products are those of `PowerSeries`. All natural indices, including zero,
are included. Only the exponential-series assertion requires a ℚ-algebra.
-/

noncomputable section

universe u

namespace Specs.FiniteCombinatorics.Series.CoefficientAlgebra

open scoped BigOperators

/-- Cauchy's coefficient formula over every commutative ring. -/
def CauchyProduct : Prop :=
  ∀ {R : Type u} [CommRing R] (A B : PowerSeries R) (n : ℕ),
    PowerSeries.coeff n (A * B) =
      ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i A * PowerSeries.coeff (n - i) B

/-- Formal differentiation is the coefficient-shift operator. -/
def DerivativeCoefficients : Prop :=
  ∀ {R : Type u} [CommRing R] (A : PowerSeries R) (n : ℕ),
    PowerSeries.coeff n (PowerSeries.derivative A) =
      (n + 1 : R) * PowerSeries.coeff (n + 1) A

/-- Leibniz's rule for formal power series. -/
def DerivativeProduct : Prop :=
  ∀ {R : Type u} [CommRing R] (A B : PowerSeries R),
    PowerSeries.derivative (A * B) =
      PowerSeries.derivative A * B + A * PowerSeries.derivative B

/-- Constants differentiate to zero, including over rings of positive characteristic. -/
def DerivativeConstant : Prop :=
  ∀ {R : Type u} [CommRing R] (r : R),
    PowerSeries.derivative (PowerSeries.C r) = 0

/-- Cauchy's formula specialized to the shared OGF construction. -/
def OGFProductCoefficients : Prop :=
  ∀ {R : Type u} [CommRing R] (a b : ℕ → R) (n : ℕ),
    PowerSeries.coeff n (ogfValue a * ogfValue b) =
      ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

/-- Differentiation specialized to the shared OGF construction. -/
def OGFDerivativeCoefficients : Prop :=
  ∀ {R : Type u} [CommRing R] (a : ℕ → R) (n : ℕ),
    PowerSeries.coeff n (PowerSeries.derivative (ogfValue a)) =
      (n + 1 : R) * a (n + 1)

/-- The EGF product is the EGF of the binomial convolution.
Natural binomial coefficients are mapped to R by its canonical natural cast;
reciprocal factorials are mapped from ℚ by the shared EGF definition. -/
def EGFProduct : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (a b : ℕ → R),
    egfValue a * egfValue b =
      egfValue (fun n => ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : R) * a i * b (n - i))

end Specs.FiniteCombinatorics.Series.CoefficientAlgebra
