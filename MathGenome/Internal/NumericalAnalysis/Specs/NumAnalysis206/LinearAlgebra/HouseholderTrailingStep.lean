import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderReflector
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.DotProduct

/-! W32, trailing-tail update (paper.tex 1140–1148, 1191–1230), with the
adopted admissible-budget hypothesis d*u < 1. All vectors contain exact stored
real values. The abstract model allows any rounding map on its stated domain. -/
noncomputable section
open scoped BigOperators
namespace NumAnalysis206.HouseholderTrailingDefinitions
open MatrixDefinitions Rounding

/-- Either W07 evaluation form can be chosen independently for the two dots. -/
def numerator {d : ℕ} (fused : Bool) (round : ℝ → ℝ) (w y : Vec ℝ d) : ℝ :=
  DotSpecs.finiteTrace fused round (⇑w) (⇑y)

def denominator {d : ℕ} (fused : Bool) (round : ℝ → ℝ) (w : Vec ℝ d) : ℝ :=
  DotSpecs.finiteTrace fused round (⇑w) (⇑w)

def scale {d : ℕ} (fp fq : Bool) (round : ℝ → ℝ) (w y : Vec ℝ d) : ℝ :=
  round (round (2 * numerator fp round w y) / denominator fq round w)

def update {d : ℕ} (fp fq : Bool) (round : ℝ → ℝ) (w y : Vec ℝ d) : Vec ℝ d :=
  WithLp.toLp 2 (fun i => round (y i - round (scale fp fq round w y * w i)))

/-- Range checks for precisely the executed primitives. Positivity of the
computed denominator is a conclusion, not an assumption of this predicate. -/
def Safe {d : ℕ} (fp fq : Bool) (round : ℝ → ℝ) (D : Set ℝ) (w y : Vec ℝ d) : Prop :=
  DotSpecs.finiteSafe fp round D (⇑w) (⇑y) ∧
  DotSpecs.finiteSafe fq round D (⇑w) (⇑w) ∧
  2 * numerator fp round w y ∈ D ∧
  round (2 * numerator fp round w y) / denominator fq round w ∈ D ∧
  ∀ i, scale fp fq round w y * w i ∈ D ∧
    y i - round (scale fp fq round w y * w i) ∈ D

def R₀ (g u : ℝ) : ℝ := (1 + u) ^ 2 / (1 - g)
def D₀ (g u : ℝ) : ℝ := max (R₀ g u - 1) (1 - (1 - u) ^ 2 / (1 + g))
def ctail (g u : ℝ) : ℝ :=
  2 * (D₀ g u + R₀ g u * g) + u + 2 * (2 * u + u ^ 2) * R₀ g u * (1 + g)

end NumAnalysis206.HouseholderTrailingDefinitions

namespace Specs.NumAnalysis206.HouseholderTrailingStep
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.HouseholderTrailingDefinitions

def trailing_step : Prop := ∀ {d : ℕ} (fp fq : Bool) (round : ℝ → ℝ)
    (u : ℝ) (D : Set ℝ) (w y : Vec ℝ d),
  w ≠ 0 → _root_.NumAnalysis206.Rounding.Specs.RelativeModelValue round u D →
  (d : ℝ) * u < 1 → _root_.Specs.NumAnalysis206.Rounding.gammaValue d u < 1 →
  Safe fp fq round D w y →
  0 < denominator fq round w ∧
  ‖update fp fq round w y -
      (_root_.NumAnalysis206.HouseholderDefinitions.reflector w).toEuclideanLin y‖ ≤
    ctail (_root_.Specs.NumAnalysis206.Rounding.gammaValue d u) u * ‖y‖

end Specs.NumAnalysis206.HouseholderTrailingStep
