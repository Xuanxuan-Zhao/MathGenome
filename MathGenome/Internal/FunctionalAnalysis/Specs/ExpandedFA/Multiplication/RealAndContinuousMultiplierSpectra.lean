import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.LpMultiplierSpectrum
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-! Remaining clauses of `fa2:p3:lp-multiplication-spectrum`, paper.tex:14071–14158.
Real symbols use their natural complexification, as in the accepted interface.
On an open Euclidean subset, `volume : Measure U` is Lebesgue measure pulled
back along the subtype inclusion, so symbols need only be defined on U. -/
noncomputable section
open MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
open scoped ENNReal
namespace ExpandedFA.Multiplication.RealAndContinuousMultiplierSpectraSpec

def RealSpectrum : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω), Semifinite μ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ a : Ω → ℝ, Measurable a →
  multiplierSpectrum μ p (fun x => (a x : ℂ)) ⊆ Set.range Complex.ofReal

/-- The endpoints are actual real essential infimum and supremum; essential
boundedness and a nonzero Lp space are required precisely for these clauses. -/
def BoundedRealSpectrum : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω), Semifinite μ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ [Nontrivial (Lp ℂ p μ)] (a : Ω → ℝ), Measurable a → MemLp a ∞ μ →
  ((essInf a μ : ℝ) : ℂ) ∈ multiplierSpectrum μ p (fun x => (a x : ℂ)) ∧
  ((essSup a μ : ℝ) : ℂ) ∈ multiplierSpectrum μ p (fun x => (a x : ℂ)) ∧
  multiplierSpectrum μ p (fun x => (a x : ℂ)) ⊆
    Complex.ofReal '' Set.Icc (essInf a μ) (essSup a μ) ∧
  (multiplierSpectrum μ p (fun x => (a x : ℂ)) = {0} ↔ a =ᵐ[μ] 0)

/-- The same assertion starting with a nonzero real Lp space, with the spectrum
still taken on its natural complexification. -/
def RealSpaceBoundedSpectrum : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω), Semifinite μ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ [Nontrivial (Lp ℝ p μ)] (a : Ω → ℝ), Measurable a → MemLp a ∞ μ →
  ((essInf a μ : ℝ) : ℂ) ∈ multiplierSpectrum μ p (fun x => (a x : ℂ)) ∧
  ((essSup a μ : ℝ) : ℂ) ∈ multiplierSpectrum μ p (fun x => (a x : ℂ)) ∧
  multiplierSpectrum μ p (fun x => (a x : ℂ)) ⊆
    Complex.ofReal '' Set.Icc (essInf a μ) (essSup a μ) ∧
  (multiplierSpectrum μ p (fun x => (a x : ℂ)) = {0} ↔ a =ᵐ[μ] 0)

def ContinuousSpectrum : Prop := ∀ (n : ℕ)
  (U : Set (EuclideanSpace ℝ (Fin n))), IsOpen U → U.Nonempty →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ a : U → ℂ, Continuous a →
  multiplierSpectrum (volume : Measure U) p a = closure (Set.range a)

def LogisticRange : Prop :=
  Set.range (fun x : ℝ => (1 + Real.exp (-x))⁻¹) = Set.Ioo 0 1

def LogisticSpectrum : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  multiplierSpectrum (volume : Measure ℝ) p
    (fun x => (((1 + Real.exp (-x))⁻¹ : ℝ) : ℂ)) =
    Complex.ofReal '' Set.Icc 0 1

end ExpandedFA.Multiplication.RealAndContinuousMultiplierSpectraSpec
