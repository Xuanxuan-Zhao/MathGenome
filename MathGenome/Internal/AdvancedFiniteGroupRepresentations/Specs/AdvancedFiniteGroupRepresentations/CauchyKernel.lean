import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.PowerSumsAlternants
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.PowerSeries.Basic

/-! FR-C02, first identity (source lines 885–903). The formal variable `t`
records the common degree in the two alphabets. Thus the coefficient of `t^n`
is exactly the bidegree `(n,n)` part of the printed identity. Every coefficient
on the partition side is a finite sum over `Partition n`. No analytic convergence
or specialization of a power series at `t = 1` is used. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Two disjoint, commuting alphabets over the source's coefficient field. -/
abbrev CauchyAlphabet (r : ℕ) := MvPolynomial (Fin r ⊕ Fin r) ℂ
def CauchyAlphabetType := ℕ → Type

/-- The ordered pair of total degrees in the two alphabets. -/
def cauchyBidegreeWeight (r : ℕ) : Fin r ⊕ Fin r → ℕ × ℕ :=
  Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))
def cauchyBidegreeWeightType := (r : ℕ) → (Fin r ⊕ Fin r → ℕ × ℕ)

def xAlphabet (r : ℕ) : Alphabet r →ₐ[ℂ] CauchyAlphabet r :=
  MvPolynomial.rename Sum.inl
def xAlphabetType := (r : ℕ) → Alphabet r →ₐ[ℂ] CauchyAlphabet r

def yAlphabet (r : ℕ) : Alphabet r →ₐ[ℂ] CauchyAlphabet r :=
  MvPolynomial.rename Sum.inr
def yAlphabetType := (r : ℕ) → Alphabet r →ₐ[ℂ] CauchyAlphabet r

def pairedPowerSum (r j : ℕ) : CauchyAlphabet r :=
  xAlphabet r (powerSum r j) * yAlphabet r (powerSum r j)
def pairedPowerSumType := (r j : ℕ) → CauchyAlphabet r

def pairedPartitionPowerSum {n : ℕ} (r : ℕ) (ν : Partition n) : CauchyAlphabet r :=
  xAlphabet r (partitionPowerSum r ν) * yAlphabet r (partitionPowerSum r ν)
def pairedPartitionPowerSumType := {n : ℕ} → (r : ℕ) → Partition n → CauchyAlphabet r

/-- The formal geometric expansion of `(1 - t*x_i*y_j)⁻¹`. -/
def cauchyFactor {r : ℕ} (i j : Fin r) : PowerSeries (CauchyAlphabet r) :=
  PowerSeries.mk fun n =>
    ((MvPolynomial.X (Sum.inl i) : CauchyAlphabet r) * MvPolynomial.X (Sum.inr j)) ^ n
def cauchyFactorType := {r : ℕ} → (i j : Fin r) → PowerSeries (CauchyAlphabet r)

def cauchyKernel (r : ℕ) : PowerSeries (CauchyAlphabet r) :=
  ∏ i : Fin r, ∏ j : Fin r, cauchyFactor i j
def cauchyKernelType := (r : ℕ) → PowerSeries (CauchyAlphabet r)

/-- All cycle lengths, including ones, occur in the upstream `zFactor`. -/
def cauchyPartitionCoefficient (r n : ℕ) : CauchyAlphabet r :=
  ∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν
def cauchyPartitionCoefficientType := (r n : ℕ) → CauchyAlphabet r

def cauchyPartitionSeries (r : ℕ) : PowerSeries (CauchyAlphabet r) :=
  PowerSeries.mk (cauchyPartitionCoefficient r)
def cauchyPartitionSeriesType := (r : ℕ) → PowerSeries (CauchyAlphabet r)

/-- The first printed identity, with a variable recording common degree. -/
def cauchy_identityType : Prop := ∀ r : ℕ, 1 ≤ r →
  cauchyKernel r = cauchyPartitionSeries r

/-- The same formal identity stated degree by degree. -/
def cauchy_identity_degreeType : Prop := ∀ (r : ℕ), 1 ≤ r → ∀ n : ℕ,
  PowerSeries.coeff n (cauchyKernel r) =
    ∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν

/-- Each finite coefficient really has the common degree recorded by `t`. -/
def cauchyPartitionCoefficient_bihomogeneousType : Prop := ∀ (r n : ℕ),
  (cauchyPartitionCoefficient r n).IsWeightedHomogeneous (cauchyBidegreeWeight r) (n, n)

/-- The geometric-product kernel is the inverse of the full denominator. -/
def cauchyKernel_mul_denominatorType : Prop := ∀ r : ℕ,
  cauchyKernel r * (∏ i : Fin r, ∏ j : Fin r,
    (1 - PowerSeries.C ((MvPolynomial.X (Sum.inl i) : CauchyAlphabet r) *
      MvPolynomial.X (Sum.inr j)) * PowerSeries.X)) = 1

end Specs.AdvancedFiniteGroupRepresentations
