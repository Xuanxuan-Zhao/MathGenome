import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.BoundedUnivalent
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Extremal existence in paper.tex:2476–2479, before the surjectivity
argument of D12.12.03. The family contains all injective weakly holomorphic
maps to the open unit disk fixing the chosen point, with no derivative
normalization imposed on its membership. -/

noncomputable section

namespace Specs.D12Complex.Ch12.ExtremalUnivalent
open _root_.D12Complex

def normalizedFamily_type := Set ℂ → ℂ → Set (ℂ → ℂ)
def normalizedFamily_value : normalizedFamily_type :=
  fun Ω z₀ => {f | HolomorphicOn Ω f ∧ Set.InjOn f Ω ∧
    Set.MapsTo f Ω (Metric.ball 0 1) ∧ f z₀ = 0}

def derivativeNorms_type := Set ℂ → ℂ → Set ℝ
def derivativeNorms_value : derivativeNorms_type :=
  fun Ω z₀ => (fun f : ℂ → ℂ => ‖deriv f z₀‖) '' normalizedFamily_value Ω z₀

def derivativeSupremum_type := Set ℂ → ℂ → ℝ
def derivativeSupremum_value : derivativeSupremum_type :=
  fun Ω z₀ => sSup (derivativeNorms_value Ω z₀)

/-- For precisely the source's proper domains with universal square roots,
the nonempty derivative-norm set is bounded above, its supremum is positive,
and an injection into the open disk attains it as a positive real derivative.
No surjectivity or prior simple-connectivity premise is asserted. -/
def extremal_univalent_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → Ω ≠ Set.univ →
    (∀ g : ℂ → ℂ, HolomorphicOn Ω g → (∀ z ∈ Ω, g z ≠ 0) →
      ∃ s : ℂ → ℂ, HolomorphicOn Ω s ∧ ∀ z ∈ Ω, (s z) ^ 2 = g z) →
    ∀ z₀ ∈ Ω,
      (derivativeNorms_value Ω z₀).Nonempty ∧ BddAbove (derivativeNorms_value Ω z₀) ∧
      0 < derivativeSupremum_value Ω z₀ ∧
      ∃ F : ℂ → ℂ, F ∈ normalizedFamily_value Ω z₀ ∧
        deriv F z₀ = (derivativeSupremum_value Ω z₀ : ℂ)

end Specs.D12Complex.Ch12.ExtremalUnivalent
