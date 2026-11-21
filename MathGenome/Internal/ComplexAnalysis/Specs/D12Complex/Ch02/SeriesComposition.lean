import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.SeriesAlgebra
import Mathlib.Combinatorics.Enumerative.Composition

open Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace D12Complex.SeriesComposition

/-- A term of formal substitution, indexed by an ordered decomposition of
its total degree into positive degrees. The empty decomposition gives d₀. -/
def substitutionTerm (c d : ℕ → ℂ) {n : ℕ} (k : Composition n) : ℂ :=
  d k.length * ∏ j, c (k.blocksFun j)

/-- The finite coefficient obtained by collecting all terms of the same degree.
Only positive-degree coefficients of the inner series occur. -/
def substitutedCoefficients (c d : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k : Composition n, substitutionTerm c d k

/-- Absolute value majorant for F(a+w)-F(a), with its constant term removed. -/
def innerMajorant (c : ℕ → ℂ) (r : ℝ) : ℝ :=
  ∑' n, if n = 0 then 0 else ‖c n‖ * r ^ n

end D12Complex.SeriesComposition

namespace Specs.D12Complex.Ch02.SeriesComposition
open _root_.D12Complex _root_.D12Complex.SeriesComposition _root_.D12Complex.SeriesAlgebra

def substitutionTerm_type := (ℕ → ℂ) → (ℕ → ℂ) → {n : ℕ} → Composition n → ℂ
def substitutionTerm_value : substitutionTerm_type :=
  fun c d _ k => d k.length * ∏ j, c (k.blocksFun j)
def substitutedCoefficients_type := (ℕ → ℂ) → (ℕ → ℂ) → ℕ → ℂ
def substitutedCoefficients_value : substitutedCoefficients_type :=
  fun c d n => ∑ k : Composition n, substitutionTerm c d k
def innerMajorant_type := (ℕ → ℂ) → ℝ → ℝ
def innerMajorant_value : innerMajorant_type :=
  fun c r => ∑' n, if n = 0 then 0 else ‖c n‖ * r ^ n

/-- Local representations are hypotheses about actual convergent scalar series.
The result includes the ungrouped absolute expansion, regrouping by degree,
and uniform convergence of both series and absolute-value series on a closed
positive disk. No nonconstancy hypothesis is imposed on F. -/
def composition_type : Prop :=
  ∀ (F G : ℂ → ℂ) (a b : ℂ) (c d : ℕ → ℂ), F a = b →
    (∀ᶠ z in 𝓝 a, HasSum (fun n => c n * (z - a) ^ n) (F z)) →
    (∀ᶠ z in 𝓝 b, HasSum (fun n => d n * (z - b) ^ n) (G z)) →
    ∃ r : ℝ, 0 < r ∧
      Summable (fun n => if n = 0 then 0 else ‖c n‖ * r ^ n) ∧
      ENNReal.ofReal (innerMajorant c r) < powerSeriesRadius d ∧
      Summable (fun i : Σ n, Composition n => ‖substitutionTerm c d i.2‖ * r ^ i.1) ∧
      (∀ z ∈ Metric.closedBall a r,
        HasSum (fun i : Σ n, Composition n => substitutionTerm c d i.2 * (z - a) ^ i.1)
          (G (F z))) ∧
      TendstoUniformlyOn
        (fun s : Finset (Σ n, Composition n) => fun z =>
          ∑ i ∈ s, substitutionTerm c d i.2 * (z - a) ^ i.1)
        (fun z => G (F z)) atTop (Metric.closedBall a r) ∧
      TendstoUniformlyOn
        (fun s : Finset (Σ n, Composition n) => fun z =>
          ∑ i ∈ s, ‖substitutionTerm c d i.2 * (z - a) ^ i.1‖)
        (fun z => ∑' i : Σ n, Composition n,
          ‖substitutionTerm c d i.2 * (z - a) ^ i.1‖)
        atTop (Metric.closedBall a r) ∧
      (∀ z ∈ Metric.closedBall a r,
        HasSum (fun n => substitutedCoefficients c d n * (z - a) ^ n) (G (F z))) ∧
      AbsoluteUniformOnDisk (substitutedCoefficients c d) a r (fun z => G (F z))

end Specs.D12Complex.Ch02.SeriesComposition
