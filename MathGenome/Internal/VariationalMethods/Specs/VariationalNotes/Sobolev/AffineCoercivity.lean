import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology
namespace VariationalNotes.Sobolev

/-- The hypotheses used in the coercive stage of the direct method.
There is no convexity hypothesis. The lower bound may hold outside a common
null set; in particular the everywhere bound in the manuscript is covered. -/
structure CoercivityHypotheses {d m : ℕ} (Ω : Opens (Domain d))
    (p q : Exponent) (F : Domain d → Vector m → Gradient m d → ℝ)
    (α C : ℝ) (a : Domain d → ℝ) : Prop where
  bounded : Bornology.IsBounded (Ω : Set (Domain d))
  exponent_lt : q.real < p.real
  measurable : ∀ s Z, AEMeasurable (fun x => F x s Z) (domainMeasure Ω)
  continuous : ∀ᵐ x ∂domainMeasure Ω,
    Continuous (fun y : Vector m × Gradient m d => F x y.1 y.2)
  alpha_pos : 0 < α
  C_nonneg : 0 ≤ C
  a_integrable : Integrable a (domainMeasure Ω)
  lower_bound : ∀ᵐ x ∂domainMeasure Ω, ∀ s Z,
    α * ‖Z‖ ^ p.real - C * ‖s‖ ^ q.real - a x ≤ F x s Z

namespace AffineCoercivityExpected

/-- A single finite constant works for every member of the prescribed class. -/
def Estimate : Prop :=
  ∀ {d m : ℕ} [NeZero d] [NeZero m] (Ω : Opens (Domain d))
    (p q : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ) (α C : ℝ) (a : Domain d → ℝ),
    CoercivityHypotheses Ω p q F α C a →
    ∃ C₂ : ℝ, ∀ u ∈ affineClass Ω m p u₀,
      ((α / 2 * ‖gradient Ω m p u‖ ^ p.real - C₂ : ℝ) : EReal) ≤ energy Ω m p F u

/-- Every finite energy upper bound gives a uniform full Sobolev norm bound. -/
def Sublevels : Prop :=
  ∀ {d m : ℕ} [NeZero d] [NeZero m] (Ω : Opens (Domain d))
    (p q : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ) (α C : ℝ) (a : Domain d → ℝ),
    CoercivityHypotheses Ω p q F α C a → ∀ M : ℝ,
    Bornology.IsBounded {u ∈ affineClass Ω m p u₀ | energy Ω m p F u ≤ (M : EReal)}

/-- A finite competitor gives a real infimum and a norm bounded minimizing
sequence. Each term has finite energy, and its extended energy tends to that
infimum. The infimum is taken over the entire affine class, including +∞ energies. -/
def MinimizingSequence : Prop :=
  ∀ {d m : ℕ} [NeZero d] [NeZero m] (Ω : Opens (Domain d))
    (p q : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ) (α C : ℝ) (a : Domain d → ℝ),
    CoercivityHypotheses Ω p q F α C a →
    (∃ v ∈ affineClass Ω m p u₀, ∃ e : ℝ, energy Ω m p F v = (e : EReal)) →
    ∃ I : ℝ, sInf (energy Ω m p F '' affineClass Ω m p u₀) = (I : EReal) ∧
      ∃ u : ℕ → W1p Ω m p,
        (∀ n, u n ∈ affineClass Ω m p u₀) ∧
        (∀ n, ∃ e : ℝ, energy Ω m p F (u n) = (e : EReal)) ∧
        Bornology.IsBounded (Set.range u) ∧
        Tendsto (fun n => energy Ω m p F (u n)) atTop (𝓝 (I : EReal))

end AffineCoercivityExpected
end VariationalNotes.Sobolev
