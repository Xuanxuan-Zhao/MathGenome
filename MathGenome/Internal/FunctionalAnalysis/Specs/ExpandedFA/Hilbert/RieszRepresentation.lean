import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-!
Independent statements for `paper.tex` 7444–7450, `fa2:p2:riesz`.
The dual is the shared continuous scalar-linear dual. The forms use the
shared conjugate-first convention and their native operator norm, which the
conventions interface identifies with the least nonnegative form bound.
There is no nontriviality, dimension, or separability hypothesis.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.RieszRepresentation.Spec
universe u v

/-- Existence, exact norm, and uniqueness among all representing vectors. -/
def FunctionalRepresentation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (f : H →L[𝕜] 𝕜),
    ∃ h : H, (∀ x : H, f x = ⟪h, x⟫_𝕜) ∧ ‖f‖ = ‖h‖ ∧
      ∀ k : H, (∀ x : H, f x = ⟪k, x⟫_𝕜) → k = h

/-- Every bounded conjugate-first form has a unique bounded scalar-linear
representing operator in the second slot, with exactly the form's norm. -/
def FormRepresentation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H),
    ∃ A : H →L[𝕜] H, (∀ x y : H, a x y = ⟪x, A y⟫_𝕜) ∧ ‖A‖ = ‖a‖ ∧
      ∀ B : H →L[𝕜] H, (∀ x y : H, a x y = ⟪x, B y⟫_𝕜) → B = A

end ExpandedFA.Hilbert.RieszRepresentation.Spec
