import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact

/-! Independent statements of paper.tex:2750–2755 (D12.15.06). -/

noncomputable section
open Set

namespace D12Complex.PolynomialHull.Definitions

/-- Polynomial inequalities defining the planar polynomial hull. Real empty
suprema are zero; consequently the constant polynomial one excludes every
point from the hull of the empty set, as stipulated in the source. -/
def polynomialHull (K : Set ℂ) : Set ℂ :=
  {a | ∀ p : Polynomial ℂ, ‖p.eval a‖ ≤ sSup ((fun z => ‖p.eval z‖) '' K)}

end D12Complex.PolynomialHull.Definitions

namespace Specs.D12Complex.Ch15.PolynomialHull
open _root_.D12Complex.PolynomialHull.Definitions

def polynomialHull_type := Set ℂ → Set ℂ
def polynomialHull_value : polynomialHull_type := fun K =>
  {a | ∀ p : Polynomial ℂ, ‖p.eval a‖ ≤ sSup ((fun z => ‖p.eval z‖) '' K)}

def subset_polynomialHull_type : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ polynomialHull K

/-- The maximum-modulus direction, with no smoothness or connectedness
assumption on K. A complementary component is indexed by one of its points. -/
def bounded_component_subset_polynomialHull_type : Prop :=
  ∀ (K : Set ℂ), IsCompact K → K.Nonempty →
    ∀ a : ℂ, a ∉ K → Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      connectedComponentIn Kᶜ a ⊆ polynomialHull K

/-- A polynomial separating every point in an unbounded complementary
component, normalized to one there and uniformly bounded by one half on K. -/
def polynomial_separation_type : Prop :=
  ∀ (K : Set ℂ), IsCompact K → K.Nonempty →
    ∀ a : ℂ, a ∉ K → ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      ∃ q : Polynomial ℂ, q.eval a = 1 ∧
        sSup ((fun z => ‖q.eval z‖) '' K) ≤ (1 / 2 : ℝ)

def polynomialHull_eq_filledHoles_type : Prop :=
  ∀ (K : Set ℂ), IsCompact K → K.Nonempty →
    polynomialHull K = K ∪
      {a | a ∉ K ∧ Bornology.IsBounded (connectedComponentIn Kᶜ a)}

def polynomialHull_empty_type : Prop := polynomialHull ∅ = ∅

end Specs.D12Complex.Ch15.PolynomialHull
