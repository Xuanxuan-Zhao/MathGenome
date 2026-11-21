import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CauchyKernel

/-! FR-C02, second identity and its coefficient consequence (source 885–923).
The upstream formal variable records common degree. After multiplication by
both Vandermonde polynomials its coefficient numbered `n` has bidegree
`(n + staircaseDegree r, n + staircaseDegree r)`. On the partition side the
same coefficient is the finite sum over partitions of `n`, with at most `r`
rows. Thus no infinite sum of polynomials or substitution `t = 1` is used.
All determinants retain the upstream descending-column convention. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The exponent vector of a partition padded by zeros and shifted by δ. -/
def shiftedPartition {n : ℕ} (r : ℕ) (ν : Partition n) : Fin r → ℕ :=
  fun i => rowLength ν i.val + staircase r i
def shiftedPartitionType := {n : ℕ} → (r : ℕ) → Partition n → Fin r → ℕ

def staircaseDegree (r : ℕ) : ℕ := ∑ i : Fin r, staircase r i
def staircaseDegreeType := ℕ → ℕ

def partitionAlternant {n : ℕ} (r : ℕ) (ν : Partition n) : Alphabet r :=
  alternant (shiftedPartition r ν)
def partitionAlternantType := {n : ℕ} → (r : ℕ) → Partition n → Alphabet r

def pairedPartitionAlternant {n : ℕ} (r : ℕ) (ν : Partition n) : CauchyAlphabet r :=
  xAlphabet r (partitionAlternant r ν) * yAlphabet r (partitionAlternant r ν)
def pairedPartitionAlternantType := {n : ℕ} → (r : ℕ) → Partition n → CauchyAlphabet r

def alternatingPartitionCoefficient (r n : ℕ) : CauchyAlphabet r :=
  ∑ ν : Partition n, if length ν ≤ r then pairedPartitionAlternant r ν else 0
def alternatingPartitionCoefficientType := (r n : ℕ) → CauchyAlphabet r

def alternatingPartitionSeries (r : ℕ) : PowerSeries (CauchyAlphabet r) :=
  PowerSeries.mk (alternatingPartitionCoefficient r)
def alternatingPartitionSeriesType := (r : ℕ) → PowerSeries (CauchyAlphabet r)

def pairedVandermonde (r : ℕ) : CauchyAlphabet r :=
  xAlphabet r (vandermonde r) * yAlphabet r (vandermonde r)
def pairedVandermondeType := (r : ℕ) → CauchyAlphabet r

def alternatingCauchyKernel (r : ℕ) : PowerSeries (CauchyAlphabet r) :=
  PowerSeries.C (pairedVandermonde r) * cauchyKernel r
def alternatingCauchyKernelType := (r : ℕ) → PowerSeries (CauchyAlphabet r)

/-- Ordinary coefficient extraction in the two disjoint alphabets. -/
def pairedNaturalCoefficient {r : ℕ} (a b : Fin r → ℕ)
    (p : CauchyAlphabet r) : ℂ :=
  p.coeff (Finsupp.equivFunOnFinite.symm (Sum.elim a b))
def pairedNaturalCoefficientType := {r : ℕ} →
  (Fin r → ℕ) → (Fin r → ℕ) → CauchyAlphabet r → ℂ

/-- The second printed identity, with `t` recording degree above δ. -/
def alternating_cauchy_identityType : Prop := ∀ r : ℕ, 1 ≤ r →
  alternatingCauchyKernel r = alternatingPartitionSeries r

def alternating_cauchy_identity_degreeType : Prop := ∀ r : ℕ, 1 ≤ r → ∀ n : ℕ,
  pairedVandermonde r * PowerSeries.coeff n (cauchyKernel r) =
    alternatingPartitionCoefficient r n

/-- This makes the degreewise interpretation of the partition sum explicit. -/
def alternatingPartitionCoefficient_bihomogeneousType : Prop := ∀ r n : ℕ,
  (alternatingPartitionCoefficient r n).IsWeightedHomogeneous
    (cauchyBidegreeWeight r) (n + staircaseDegree r, n + staircaseDegree r)

def alternatingCauchyKernel_bihomogeneousType : Prop := ∀ r : ℕ, 1 ≤ r → ∀ n : ℕ,
  (PowerSeries.coeff n (alternatingCauchyKernel r)).IsWeightedHomogeneous
    (cauchyBidegreeWeight r) (n + staircaseDegree r, n + staircaseDegree r)

/-- The two partitions may have different sizes. Diagram equality compares
shapes independently of the dependent index `n`. This is exactly equality of
the original partitions when the indices agree. The series coefficient `n`
is the unique possible common degree for the requested x-exponent. -/
def alternating_cauchy_coefficientType : Prop := ∀ (r : ℕ), 1 ≤ r →
  ∀ {n m : ℕ} (lam : Partition n) (μ : Partition m), length lam ≤ r → length μ ≤ r →
  pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
    (PowerSeries.coeff n (alternatingCauchyKernel r)) =
      if diagram lam = diagram μ then 1 else 0

end Specs.AdvancedFiniteGroupRepresentations
