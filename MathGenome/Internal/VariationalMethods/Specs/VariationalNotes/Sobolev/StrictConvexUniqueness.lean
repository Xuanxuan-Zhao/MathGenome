import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.Convex.Function

/-! Independent statements of paper.tex, prop:sobolev-unique (3949–3971).
Measurable energy densities (in particular the chapter's finite Carathéodory
integrands) are used with the signed extended integral: competitors may have energy +∞. Only the first minimizer is required
to have finite energy; the second is any global minimizer. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Sobolev.UniquenessExpected

def Joint : Prop :=
  ∀ {d m : ℕ}, 0 < d → 0 < m →
  ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ),
    (∀ w ∈ affineClass Ω m p u₀, AEMeasurable
      (fun x => F x (value Ω m p w x) (gradient Ω m p w x)) (domainMeasure Ω)) →
    (∀ᵐ x ∂domainMeasure Ω,
      StrictConvexOn ℝ univ (fun y : Vector m × Gradient m d => F x y.1 y.2)) →
    (∀ u ∈ affineClass Ω m p u₀,
      CaratheodorySpecs.NegativePartIntegrable (domainMeasure Ω)
        (fun x => F x (value Ω m p u x) (gradient Ω m p u x))) →
    ∀ u ∈ affineClass Ω m p u₀, ∀ c : ℝ, energy Ω m p F u = (c : EReal) →
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F w) →
    ∀ v ∈ affineClass Ω m p u₀,
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F v ≤ energy Ω m p F w) → u = v

/-- Independence of the state is expressed for the original three-argument
integrand, without replacing the given energy or its admissible class. -/
def GradientOnly : Prop :=
  ∀ {d m : ℕ}, 0 < d → 0 < m →
  ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ),
    (∀ w ∈ affineClass Ω m p u₀, AEMeasurable
      (fun x => F x (value Ω m p w x) (gradient Ω m p w x)) (domainMeasure Ω)) →
    (∀ᵐ x ∂domainMeasure Ω, ∀ s t Z, F x s Z = F x t Z) →
    (∀ᵐ x ∂domainMeasure Ω, StrictConvexOn ℝ univ (F x 0)) →
    (∀ u ∈ affineClass Ω m p u₀,
      CaratheodorySpecs.NegativePartIntegrable (domainMeasure Ω)
        (fun x => F x (value Ω m p u x) (gradient Ω m p u x))) →
    ∀ u ∈ affineClass Ω m p u₀, ∀ c : ℝ, energy Ω m p F u = (c : EReal) →
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F w) →
    ∀ v ∈ affineClass Ω m p u₀,
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F v ≤ energy Ω m p F w) → u = v


/-- Specializations to the chapter's Carathéodory convention. -/
def JointCaratheodory : Prop :=
  ∀ {d m : ℕ}, 0 < d → 0 < m →
  ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ),
    CaratheodorySpecs.Caratheodory (domainMeasure Ω)
      (fun x (y : Vector m × Gradient m d) => F x y.1 y.2) →
    (∀ᵐ x ∂domainMeasure Ω,
      StrictConvexOn ℝ univ (fun y : Vector m × Gradient m d => F x y.1 y.2)) →
    (∀ u ∈ affineClass Ω m p u₀,
      CaratheodorySpecs.NegativePartIntegrable (domainMeasure Ω)
        (fun x => F x (value Ω m p u x) (gradient Ω m p u x))) →
    ∀ u ∈ affineClass Ω m p u₀, ∀ c : ℝ, energy Ω m p F u = (c : EReal) →
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F w) →
    ∀ v ∈ affineClass Ω m p u₀,
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F v ≤ energy Ω m p F w) → u = v

/-- Independence of the state is expressed for the original three-argument
integrand, without replacing the given energy or its admissible class. -/
def GradientOnlyCaratheodory : Prop :=
  ∀ {d m : ℕ}, 0 < d → 0 < m →
  ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ),
    CaratheodorySpecs.Caratheodory (domainMeasure Ω)
      (fun x (y : Vector m × Gradient m d) => F x y.1 y.2) →
    (∀ᵐ x ∂domainMeasure Ω, ∀ s t Z, F x s Z = F x t Z) →
    (∀ᵐ x ∂domainMeasure Ω, StrictConvexOn ℝ univ (F x 0)) →
    (∀ u ∈ affineClass Ω m p u₀,
      CaratheodorySpecs.NegativePartIntegrable (domainMeasure Ω)
        (fun x => F x (value Ω m p u x) (gradient Ω m p u x))) →
    ∀ u ∈ affineClass Ω m p u₀, ∀ c : ℝ, energy Ω m p F u = (c : EReal) →
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F w) →
    ∀ v ∈ affineClass Ω m p u₀,
    (∀ w ∈ affineClass Ω m p u₀, energy Ω m p F v ≤ energy Ω m p F w) → u = v

end VariationalNotes.Sobolev.UniquenessExpected
