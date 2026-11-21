import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Analyticity

/-!
The local argument in K03.13.identity, paper.tex:1447–1449.
Both scalar codomains have real domain and real-variable expansions. The
coefficient sequence is the given expansion, not an independently chosen one.
Accumulating zeros are distinct from the center and occur arbitrarily close.
The global identity principle is allocated to the separate Identity goal.
-/
namespace Specs.SingleVariableAnalysis.Ch13.IsolatedZeros
open Analyticity

noncomputable def realLocalDichotomy : Prop :=
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAtValue a f c →
    ((∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ∨
    ∃ m : ℕ, (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧ ∃ g : ℝ → ℝ,
      RealPowerSeriesRepresentsAtValue (fun n => a (n+m)) g c ∧ g c = a m ∧
      ∃ δ : ℝ, 0 < δ ∧ ContinuousOn g {x | |x-c| < δ} ∧
        ∀ x, |x-c| < δ → f x = (x-c)^m * g x ∧ g x ≠ 0

noncomputable def complexRealLocalDichotomy : Prop :=
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAtValue a f c →
    ((∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ∨
    ∃ m : ℕ, (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧ ∃ g : ℝ → ℂ,
      ComplexRealPowerSeriesRepresentsAtValue (fun n => a (n+m)) g c ∧ g c = a m ∧
      ∃ δ : ℝ, 0 < δ ∧ ContinuousOn g {x | |x-c| < δ} ∧
        ∀ x, |x-c| < δ → f x = ((x-c : ℝ) : ℂ)^m * g x ∧ g x ≠ 0

noncomputable def realLocallyZeroIff : Prop :=
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAtValue a f c →
    ((∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ↔ ∀ n, a n = 0)

noncomputable def complexRealLocallyZeroIff : Prop :=
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAtValue a f c →
    ((∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ↔ ∀ n, a n = 0)

noncomputable def realIsolatedZero : Prop :=
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAtValue a f c →
    f c = 0 → (∃ n, a n ≠ 0) →
    ∃ m : ℕ, 0 < m ∧ (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < |x-c| → |x-c| < δ → f x ≠ 0

noncomputable def complexRealIsolatedZero : Prop :=
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAtValue a f c →
    f c = 0 → (∃ n, a n ≠ 0) →
    ∃ m : ℕ, 0 < m ∧ (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < |x-c| → |x-c| < δ → f x ≠ 0

noncomputable def realZeroOfAccumulation : Prop :=
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAtValue a f c →
    (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, 0 < |x-c| ∧ |x-c| < ε ∧ f x = 0) →
    (∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0

noncomputable def complexRealZeroOfAccumulation : Prop :=
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAtValue a f c →
    (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, 0 < |x-c| ∧ |x-c| < ε ∧ f x = 0) →
    (∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0

end Specs.SingleVariableAnalysis.Ch13.IsolatedZeros
