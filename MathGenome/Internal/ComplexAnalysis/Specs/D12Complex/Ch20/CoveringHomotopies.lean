import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CoveringPaths

/-! Independent statements for the homotopy part of paper.tex, d12:20-05.
The first coordinate is path time and the second is the homotopy parameter.
Both spaces are arbitrary topological spaces. -/

namespace Specs.D12Complex.Ch20.CoveringHomotopies

open unitInterval

universe u v

/-- A fixed-endpoint homotopy has exactly one continuous lift with the
prescribed constant initial edge. Equality of lifts is equality on the square. -/
def homotopy_lifting : Prop :=
  ∀ {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), D12Complex.Ch20.IsCovering p →
    ∀ (H : I × I → B), Continuous H → ∀ a b : B,
      (∀ s, H (0, s) = a) → (∀ s, H (1, s) = b) →
      ∀ e₀ : E, p e₀ = a →
        ∃! F : I × I → E, Continuous F ∧ (∀ s, F (0, s) = e₀) ∧ p ∘ F = H

/-- Each restriction of a continuous lifted square to fixed homotopy
parameter is the unique continuous path lift from the chosen initial point.
This holds even without the fixed-terminal-edge assumption. -/
def restriction_path_lifting : Prop :=
  ∀ {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), D12Complex.Ch20.IsCovering p →
    ∀ (H : I × I → B) (e₀ : E) (F : I × I → E),
      Continuous F → (∀ s, F (0, s) = e₀) → p ∘ F = H →
      ∀ s : I,
        Continuous (fun t => F (t, s)) ∧ F (0, s) = e₀ ∧
          p ∘ (fun t => F (t, s)) = (fun t => H (t, s)) ∧
          ∀ Γ : I → E, Continuous Γ → Γ 0 = e₀ →
            p ∘ Γ = (fun t => H (t, s)) → Γ = (fun t => F (t, s))

/-- The endpoints of the lifted paths are independent of the homotopy
parameter whenever the terminal edge in the base is constant. -/
def lifted_endpoints : Prop :=
  ∀ {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), D12Complex.Ch20.IsCovering p →
    ∀ (H : I × I → B) (b : B), (∀ s, H (1, s) = b) →
      ∀ F : I × I → E, Continuous F → p ∘ F = H →
        ∀ s s' : I, F (1, s) = F (1, s')

end Specs.D12Complex.Ch20.CoveringHomotopies
