import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statements for the circle moment theorem, paper.tex,
`fa2:p4:circle-moment`. A `Measure Circle` is a positive Borel measure;
finiteness is imposed explicitly. Integer powers use the complex embedding
of the unit circle. Finite subsets of integer indices describe all finite
principal Toeplitz quadratic forms (and allow zero coefficients). -/

noncomputable section

namespace ExpandedFA.PartIV.CircleMoments

open MeasureTheory
open scoped ComplexConjugate

def Hermitian (c : ℤ → ℂ) : Prop := ∀ n, c (-n) = conj (c n)

def toeplitzForm (c : ℤ → ℂ) (s : Finset ℤ) (a : ℤ → ℂ) : ℂ :=
  ∑ j ∈ s, ∑ k ∈ s, conj (a j) * a k * c (k - j)

/-- Nonnegativity as a real complex number, with no implicit order convention. -/
def ToeplitzNonnegative (c : ℤ → ℂ) : Prop :=
  ∀ s a, (toeplitzForm c s a).im = 0 ∧ 0 ≤ (toeplitzForm c s a).re

def moment (μ : Measure Circle) (n : ℤ) : ℂ := ∫ z : Circle, (z : ℂ) ^ n ∂μ

def Represents (c : ℤ → ℂ) (μ : Measure Circle) : Prop :=
  IsFiniteMeasure μ ∧ ∀ n, c n = moment μ n

namespace Spec

def CircleMomentTheorem : Prop :=
  ∀ c : ℤ → ℂ, Hermitian c →
    (ToeplitzNonnegative c ↔ ∃! μ : Measure Circle, Represents c μ)

def Necessity : Prop :=
  ∀ (c : ℤ → ℂ) (μ : Measure Circle), Represents c μ →
    Hermitian c ∧ ToeplitzNonnegative c

def Uniqueness : Prop :=
  ∀ (c : ℤ → ℂ) (μ ν : Measure Circle), Represents c μ → Represents c ν → μ = ν

def Mass : Prop :=
  ∀ (c : ℤ → ℂ) (μ : Measure Circle), Represents c μ →
    c 0 = (μ.real Set.univ : ℂ) ∧ μ Set.univ = ENNReal.ofReal (c 0).re

def ZeroSequence : Prop :=
  ∀ c : ℤ → ℂ, Hermitian c → ToeplitzNonnegative c → c 0 = 0 → c = 0

def ZeroMeasure : Prop :=
  ∀ (c : ℤ → ℂ) (μ : Measure Circle), Represents c μ → c 0 = 0 → μ = 0

end Spec
end ExpandedFA.PartIV.CircleMoments
