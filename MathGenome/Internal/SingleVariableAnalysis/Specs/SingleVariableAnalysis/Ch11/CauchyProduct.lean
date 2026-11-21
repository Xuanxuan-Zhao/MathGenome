import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute

/-!
Independent specification of K03.11.cauchy_product, paper.tex:1111–1124.
All series are ordinary limits of inclusive partial sums, indexed from zero.
In Mertens' theorem only the first factor is assumed absolutely convergent;
the second factor has its specified ordinary finite sum. Absolute convergence
of the product is a separate conclusion when both factors are absolute.
-/

namespace Specs.SingleVariableAnalysis.Ch11.CauchyProduct

open PartialSums Absolute
open scoped BigOperators

def realCauchyProductType : Type := (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ
noncomputable def realCauchyProductValue : realCauchyProductType :=
  fun a b n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

def complexCauchyProductType : Type := (ℕ → ℂ) → (ℕ → ℂ) → ℕ → ℂ
noncomputable def complexCauchyProductValue : complexCauchyProductType :=
  fun a b n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

def realMertens : Prop :=
  ∀ (a b : ℕ → ℝ) (A B : ℝ),
    realAbsolutelyConvergesValue a → realSeriesHasSumValue a A →
    realSeriesHasSumValue b B → realSeriesHasSumValue (realCauchyProductValue a b) (A * B)

def complexMertens : Prop :=
  ∀ (a b : ℕ → ℂ) (A B : ℂ),
    complexAbsolutelyConvergesValue a → complexSeriesHasSumValue a A →
    complexSeriesHasSumValue b B →
    complexSeriesHasSumValue (complexCauchyProductValue a b) (A * B)

def realCauchyProductAbsolute : Prop :=
  ∀ (a b : ℕ → ℝ), realAbsolutelyConvergesValue a → realAbsolutelyConvergesValue b →
    realAbsolutelyConvergesValue (realCauchyProductValue a b)

def complexCauchyProductAbsolute : Prop :=
  ∀ (a b : ℕ → ℂ), complexAbsolutelyConvergesValue a → complexAbsolutelyConvergesValue b →
    complexAbsolutelyConvergesValue (complexCauchyProductValue a b)

end Specs.SingleVariableAnalysis.Ch11.CauchyProduct
