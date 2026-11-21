import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.Lagrange

/-! Independent specifications for paper.tex W49. A nonempty finite set of
nodes represents the source's n + 1 nodes, including n = 0. Division and
inversion are operations in the arbitrary field K; no rounding is involved. -/

noncomputable section
open Polynomial

universe u v
namespace Specs.NumAnalysis206.Approximation

variable {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]

/-- The source's monic nodal product ω. -/
def nodalPolynomialValue (s : Finset ι) (x : ι → K) : K[X] :=
  ∏ i ∈ s, (X - C (x i))

def nodalPolynomialType :=
  ∀ {K : Type u} [Field K] {ι : Type v},
    Finset ι → (ι → K) → K[X]

/-- The inverse of the product of differences, exactly as in W49. -/
def barycentricWeightValue (s : Finset ι) (x : ι → K) (i : ι) : K :=
  (∏ j ∈ s.erase i, (x i - x j))⁻¹

def barycentricWeightType :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι],
    Finset ι → (ι → K) → ι → K

def nodalPolynomialMonic : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x : ι → K), (nodalPolynomialValue s x).Monic

def barycentricFirst : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x y : ι → K) (z : K),
    (∀ i ∈ s, z ≠ x i) →
    (interpolantValue s x y).eval z =
      (nodalPolynomialValue s x).eval z *
        ∑ i ∈ s, barycentricWeightValue s x i * y i / (z - x i)

def barycentricDenominatorNonzero : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x : ι → K) (z : K),
    Set.InjOn x s → s.Nonempty → (∀ i ∈ s, z ≠ x i) →
    (∑ i ∈ s, barycentricWeightValue s x i / (z - x i)) ≠ 0

def barycentricSecond : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x y : ι → K) (z : K),
    Set.InjOn x s → s.Nonempty → (∀ i ∈ s, z ≠ x i) →
    (interpolantValue s x y).eval z =
      (∑ i ∈ s, barycentricWeightValue s x i * y i / (z - x i)) /
        (∑ i ∈ s, barycentricWeightValue s x i / (z - x i))

def barycentricAtNode : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x y : ι → K), Set.InjOn x s →
    ∀ i ∈ s, (interpolantValue s x y).eval (x i) = y i

end Specs.NumAnalysis206.Approximation
