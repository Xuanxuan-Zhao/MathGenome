import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.PiLambda
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests
import Mathlib.LinearAlgebra.Pi

/-! Independent statement of paper.tex:442–467. `H` is a real submodule
of the space of all real functions. Its members are bounded everywhere,
not merely essentially bounded. Limits and monotonicity are pointwise;
the bound on a sequence is one real constant for every index and point.
The target measurable structure is exactly `generateFrom P`, with no measure
or completion. No multiplication closure, integration, or nonemptiness is
assumed. -/

open Set MeasurableSpace Filter
open scoped Topology
universe u

namespace Specs.D11.Ch01.FunctionalMonotoneClass

def functional_monotone_class : Prop :=
  ∀ {X : Type u} (P : Set (Set X)) (H : Submodule ℝ (X → ℝ)),
    (∀ s ∈ P, ∀ t ∈ P, s ∩ t ∈ P) →
    (∀ g ∈ H, ∃ C : ℝ, ∀ x, |g x| ≤ C) →
    (fun _ : X => (1 : ℝ)) ∈ H →
    (∀ A ∈ P, A.indicator (fun _ => (1 : ℝ)) ∈ H) →
    (∀ (g : ℕ → X → ℝ) (f : X → ℝ),
      (∀ n, g n ∈ H) →
      (∀ x, Monotone (fun n => g n x)) →
      (∃ C : ℝ, ∀ n x, |g n x| ≤ C) →
      (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) → f ∈ H) →
    ∀ f : X → ℝ,
      @Measurable X ℝ (generateFrom P) (borel ℝ) f →
      (∃ C : ℝ, ∀ x, |f x| ≤ C) → f ∈ H

end Specs.D11.Ch01.FunctionalMonotoneClass
