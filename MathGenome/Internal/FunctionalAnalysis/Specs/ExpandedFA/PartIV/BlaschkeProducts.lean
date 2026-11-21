import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLogModulus
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-! Blaschke part of `fa2:p4:hardy-factorization`, paper.tex:18875–18884.
The index includes one occurrence for each unit of the actual analytic vanishing
order. It includes zeros at the origin; finite and empty products use the same
unconditional product. The quotient is expressed by a holomorphic extension of
the division across the zeros, rather than Lean's pointwise `0 / 0` value. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace ExpandedFA.PartIV.BlaschkeProducts
open HardyDiskSpec

/-- Normalization positive at zero for a nonzero zero; the zero at zero gives z. -/
def factor (a z : ℂ) : ℂ :=
  if a = 0 then z else ((‖a‖ : ℂ) / a) * ((a - z) / (1 - conj a * z))

universe u

def familyProduct {ι : Type u} (a : ι → ℂ) (z : ℂ) : ℂ := ∏' j, factor (a j) z

def finiteProduct {ι : Type u} (a : ι → ℂ) (s : Finset ι) (z : ℂ) : ℂ :=
  ∏ j ∈ s, factor (a j) z

/-- The actual zeros with their analytic multiplicities, with no supplied zero
list or assumed Blaschke certificate. Nonzero Hardy functions have finite order. -/
def ZeroOccurrence (f : H2) :=
  {p : ℂ × ℕ // p.1 ∈ disk ∧ p.2 < analyticOrderNatAt (eval f) p.1}

def zeroPoint {f : H2} (j : ZeroOccurrence f) : ℂ := j.val.1

def canonicalProduct (f : H2) : ℂ → ℂ := familyProduct (@zeroPoint f)

namespace Spec

def ZeroOrdersFinite : Prop := ∀ f : H2, f ≠ 0 → ∀ z ∈ disk,
  analyticOrderAt (eval f) z ≠ ⊤

def ZerosCorrect : Prop := ∀ f : H2, f ≠ 0 → ∀ z ∈ disk,
  (∃ j : ZeroOccurrence f, zeroPoint j = z) ↔ eval f z = 0

def InnerNonzero : Prop := ∀ f : H2, IsInner f → f ≠ 0

def InnerBound : Prop := ∀ f : H2, IsInner f → ∀ z ∈ disk, ‖eval f z‖ ≤ 1

/-- The sum includes all repeated occurrences, including those at zero. -/
def ZeroSummability : Prop := ∀ f : H2, IsInner f →
  Summable (fun j : ZeroOccurrence f => 1 - ‖zeroPoint j‖)

def ZeroCountability : Prop := ∀ f : H2, IsInner f → Countable (ZeroOccurrence f)

def FactorAnalytic : Prop := ∀ a ∈ disk, AnalyticOnNhd ℂ (factor a) disk

def FactorZeros : Prop := ∀ a ∈ disk, ∀ z ∈ disk, factor a z = 0 ↔ z = a

def FactorBound : Prop := ∀ a ∈ disk, ∀ z ∈ disk, ‖factor a z‖ ≤ 1

def FactorBoundary : Prop := ∀ a ∈ disk, ∀ z : ℂ, ‖z‖ = 1 → ‖factor a z‖ = 1

/-- A quantitative compact-disk estimate, also valid when a = 0. -/
def FactorEstimate : Prop := ∀ a ∈ disk, ∀ r : ℝ, 0 ≤ r → r < 1 →
  ∀ z : ℂ, ‖z‖ ≤ r →
    ‖factor a z - 1‖ ≤ ((1 + r) / (1 - r)) * (1 - ‖a‖)

/-- A generic construction, without assuming the family came from a function.
Arbitrary index types include every finite, empty and infinite zero family. -/
def FamilyConvergence : Prop := ∀ (ι : Type) (a : ι → ℂ),
  (∀ j, a j ∈ disk) → Summable (fun j => 1 - ‖a j‖) →
  HasProdLocallyUniformlyOn (fun j => factor (a j)) (familyProduct a) disk

def FamilyHolomorphic : Prop := ∀ (ι : Type) (a : ι → ℂ),
  (∀ j, a j ∈ disk) → Summable (fun j => 1 - ‖a j‖) →
  DifferentiableOn ℂ (familyProduct a) disk

def FamilyZeros : Prop := ∀ (ι : Type) (a : ι → ℂ),
  (∀ j, a j ∈ disk) → Summable (fun j => 1 - ‖a j‖) →
  ∀ z ∈ disk, familyProduct a z = 0 ↔ ∃ j, z = a j

def FamilyHardy : Prop := ∀ (ι : Type) (a : ι → ℂ),
  (∀ j, a j ∈ disk) → Summable (fun j => 1 - ‖a j‖) →
  ∃ b : H2, Set.EqOn (eval b) (familyProduct a) disk ∧ ‖b‖ ≤ 1

def FamilyInner : Prop := ∀ (ι : Type) (a : ι → ℂ),
  (∀ j, a j ∈ disk) → Summable (fun j => 1 - ‖a j‖) →
  ∃ b : H2, IsInner b ∧ Set.EqOn (eval b) (familyProduct a) disk

def FiniteInner : Prop := ∀ (ι : Type) (a : ι → ℂ), (∀ j, a j ∈ disk) →
  ∀ s : Finset ι, ∃ b : H2, IsInner b ∧ Set.EqOn (eval b) (finiteProduct a s) disk

def FiniteInterpretation : Prop := ∀ (ι : Type) [Fintype ι] (a : ι → ℂ),
  familyProduct a = finiteProduct a Finset.univ

def EmptyInterpretation : Prop := ∀ (ι : Type) [IsEmpty ι] (a : ι → ℂ),
  familyProduct a = fun _ => 1

def OriginInterpretation : Prop := factor 0 = fun z => z

def CanonicalConvergence : Prop := ∀ f : H2, IsInner f →
  HasProdLocallyUniformlyOn (fun j : ZeroOccurrence f => factor (zeroPoint j))
    (canonicalProduct f) disk

def CanonicalInner : Prop := ∀ f : H2, IsInner f →
  ∃ b : H2, IsInner b ∧ Set.EqOn (eval b) (canonicalProduct f) disk

/-- Exact orders, rather than merely equality of the sets of zeros. -/
def CanonicalOrders : Prop := ∀ f : H2, IsInner f → ∀ z ∈ disk,
  analyticOrderAt (canonicalProduct f) z = analyticOrderAt (eval f) z

def ZeroFreeQuotient : Prop := ∀ f : H2, IsInner f → ∃ s : H2,
  IsInner s ∧ (∀ z ∈ disk, eval s z ≠ 0) ∧
  (∀ z ∈ disk, eval f z = canonicalProduct f z * eval s z) ∧
  (∀ z ∈ disk, canonicalProduct f z ≠ 0 → eval s z = eval f z / canonicalProduct f z)

end Spec
end ExpandedFA.PartIV.BlaschkeProducts
