import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.Compact

/-!
Independent specification of K03.16.weierstrass, paper.tex:3900–3907.
The domain is the closed real interval with its subtype topology, including
the singleton case. The norm is the canonical supremum norm on continuous
maps on that compact interval. Polynomial evaluation uses real coefficients
for real values, and complex coefficients at embedded real arguments for
complex values. No regularity beyond continuity is required.
-/
noncomputable section
open scoped Topology

namespace Specs.SingleVariableAnalysis.Ch16.Weierstrass

def realApproximation : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ (f : C(Set.Icc a b, ℝ)) (ε : ℝ), 0 < ε →
    ∃ p : Polynomial ℝ,
      ‖f - (⟨fun x => p.eval (x : ℝ),
        p.continuous.comp continuous_subtype_val⟩ : C(Set.Icc a b, ℝ))‖ < ε

def complexApproximation : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ (f : C(Set.Icc a b, ℂ)) (ε : ℝ), 0 < ε →
    ∃ p : Polynomial ℂ,
      ‖f - (⟨fun x => p.eval ((x : ℝ) : ℂ),
        p.continuous.comp (Complex.continuous_ofReal.comp continuous_subtype_val)⟩ :
          C(Set.Icc a b, ℂ))‖ < ε

end Specs.SingleVariableAnalysis.Ch16.Weierstrass
