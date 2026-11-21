import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
Independent statements of paper.tex:4132–4162 (D12.23.01).
The hypotheses concern only the open source disk. The source of univalence
is an actual plane disk of positive radius. The total inverse is constrained
on the image disk, takes its values in the source disk, and satisfies both
inverse identities there. No behavior outside the stated sets is required.
-/

namespace Specs.D12Complex.Ch23.QuantitativeBloch
open _root_.D12Complex Metric Set

def normalized_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (ball 0 1) f → deriv f 0 = 1 →
    ∃ (b : ℂ) (s : ℝ) (c : ℂ) (g : ℂ → ℂ),
      0 < s ∧ ball b s ⊆ ball 0 1 ∧ InjOn f (ball b s) ∧
      ball c (1 / 64) ⊆ f '' ball b s ∧
      HolomorphicOn (ball c (1 / 64)) g ∧
      MapsTo g (ball c (1 / 64)) (ball b s) ∧
      LeftInvOn g f (ball b s) ∧ RightInvOn g f (ball c (1 / 64))

def scaled_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ), 0 < R →
    HolomorphicOn (ball a R) f → deriv f a ≠ 0 →
    ∃ (b : ℂ) (s : ℝ) (c : ℂ) (g : ℂ → ℂ),
      0 < s ∧ ball b s ⊆ ball a R ∧ InjOn f (ball b s) ∧
      ball c (R * ‖deriv f a‖ / 64) ⊆ f '' ball b s ∧
      HolomorphicOn (ball c (R * ‖deriv f a‖ / 64)) g ∧
      MapsTo g (ball c (R * ‖deriv f a‖ / 64)) (ball b s) ∧
      LeftInvOn g f (ball b s) ∧
      RightInvOn g f (ball c (R * ‖deriv f a‖ / 64))

end Specs.D12Complex.Ch23.QuantitativeBloch
