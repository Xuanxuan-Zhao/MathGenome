import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.AffineCoercivity
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands

/-! Theorem `thm:gradient-convex-existence`, paper.tex:3885–3918.
The domain is any bounded open set, without a boundary regularity condition.
The real-valued integrand has measurable sections and is continuous and
gradient-convex off common null sets. Energies of other competitors may be +∞.
-/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Sobolev.GradientExistenceExpected

def Attainment : Prop :=
  ∀ {d m : ℕ} [NeZero d] [NeZero m] (Ω : Opens (Domain d))
    (p q : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (α C : ℝ) (a : Domain d → ℝ),
    CoercivityHypotheses Ω p q F α C a →
    (∀ s Z, Measurable (fun x => F x s Z)) →
    (∀ᵐ x ∂domainMeasure Ω, ∀ s, ConvexOn ℝ univ (F x s)) →
    (∃ v ∈ affineClass Ω m p u₀, ∃ e : ℝ, energy Ω m p F v = (e : EReal)) →
    ∃ u ∈ affineClass Ω m p u₀, ∃ e : ℝ,
      energy Ω m p F u = (e : EReal) ∧
      ∀ v ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F v

end VariationalNotes.Sobolev.GradientExistenceExpected
