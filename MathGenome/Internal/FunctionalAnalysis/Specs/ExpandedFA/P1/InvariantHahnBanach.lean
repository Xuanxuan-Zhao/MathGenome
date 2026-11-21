import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Sublinear
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Group.Subsemigroup.Defs

/-! Independent statement of `paper.tex:5282–5289`.
The semigroup need not contain the identity, and the vector space and the
invariant subspace carry no topology. All functionals are real linear. -/

universe u

namespace Specs.ExpandedFA.P1.InvariantHahnBanach

/-- The full Agnew–Morse invariant extension assertion. -/
def invariantHahnBanachType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E]
    (p : E → ℝ), Specs.ExpandedFA.P1.C05Sublinear.isSublinearValue p →
    ∀ (S : Subsemigroup (Module.End ℝ E)),
    (∀ A ∈ S, ∀ B ∈ S, Commute A B) →
    (∀ A ∈ S, ∀ x : E, p (A x) ≤ p x) →
    ∀ (Y : Submodule ℝ E)
      (hY : ∀ A ∈ S, ∀ y ∈ Y, A y ∈ Y)
      (f : Y →ₗ[ℝ] ℝ),
    (∀ y : Y, f y ≤ p (y : E)) →
    (∀ (A : Module.End ℝ E) (hA : A ∈ S) (y : Y),
      f ⟨A y, hY A hA y y.property⟩ = f y) →
    ∃ F : E →ₗ[ℝ] ℝ,
      (∀ y : Y, F (y : E) = f y) ∧
      (∀ x : E, F x ≤ p x) ∧
      (∀ A ∈ S, ∀ x : E, F (A x) = F x)

end Specs.ExpandedFA.P1.InvariantHahnBanach
