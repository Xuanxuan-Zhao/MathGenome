import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-!
Solvability and the quantitative estimate in `paper.tex` 7558–7570,
`fa2:p2:lax-milgram`. Energy minimization is a separate downstream obligation.
The forms and antiduals are the shared native continuous semilinear maps.
No nontriviality, dimension, separability, or Hermitian hypothesis is imposed.
-/

namespace ExpandedFA.Hilbert.LaxMilgramSolvability.Spec
universe u v

/-- The real/complex conjugate-first Lax–Milgram theorem, with uniqueness
among all solutions and the estimate for the specified coercivity constant. -/
def Solvability : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H) (α : ℝ),
    Conventions.Spec.FormCoerciveValue 𝕜 H a α →
    ∀ F : Conventions.Spec.ContinuousAntidualValue 𝕜 H,
      ∃ u : H, (∀ v : H, a v u = F v) ∧ ‖u‖ ≤ ‖F‖ / α ∧
        ∀ w : H, (∀ v : H, a v w = F v) → w = u

/-- The same assertion directly for continuous real bilinear forms and
continuous real linear right-hand sides. It includes the zero real space. -/
def RealSolvability : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (a : H →L[ℝ] H →L[ℝ] ℝ) (α : ℝ),
    0 < α → (∀ v : H, α * ‖v‖ ^ 2 ≤ a v v) →
    ∀ F : H →L[ℝ] ℝ,
      ∃ u : H, (∀ v : H, a v u = F v) ∧ ‖u‖ ≤ ‖F‖ / α ∧
        ∀ w : H, (∀ v : H, a v w = F v) → w = u

end ExpandedFA.Hilbert.LaxMilgramSolvability.Spec
