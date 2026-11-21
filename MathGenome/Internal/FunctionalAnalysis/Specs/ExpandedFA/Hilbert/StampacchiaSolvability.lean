import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-! Independent solvability statement for `paper.tex` 7572–7597,
`fa2:p2:stampacchia`. Convexity is over the underlying real space; the
inner product is conjugate linear in its first slot. Neither Hermitian
symmetry nor nontriviality of the Hilbert space is assumed. -/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.StampacchiaSolvability.Spec
universe u v

/-- The bounded coercive variational inequality has exactly one solution.
The datum `f` represents the conjugate-linear right-hand side `v ↦ ⟪v,f⟫`.
The constants retain the original nonnegative bound and positive coercivity. -/
def ExistenceUniqueness : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    Conventions.Spec.FormBoundValue 𝕜 H H a M →
    Conventions.Spec.FormCoerciveValue 𝕜 H a α →
    ∀ (f : H) (C : Set H), C.Nonempty → IsClosed C →
      Conventions.Spec.RealConvexValue 𝕜 H C →
      ∃! u : H, u ∈ C ∧ ∀ v ∈ C,
        RCLike.re ⟪v - u, f⟫_𝕜 ≤ RCLike.re (a (v - u) u)

end ExpandedFA.Hilbert.StampacchiaSolvability.Spec
