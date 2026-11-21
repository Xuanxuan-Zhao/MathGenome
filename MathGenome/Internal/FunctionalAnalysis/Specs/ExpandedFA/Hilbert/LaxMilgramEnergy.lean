import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-!
Lax–Milgram, paper.tex 7558–7579, fa2:p2:lax-milgram.
The energy is real-valued. Under Hermitian symmetry the diagonal agrees with
its real part, as recorded explicitly in the conclusion. No Hermitian
assumption is needed for solvability, uniqueness, or the norm estimate.
-/

noncomputable section
namespace ExpandedFA.Hilbert.LaxMilgramEnergy.Spec
universe u v

/-- The source energy, with the real interpretation of the diagonal. -/
def energy {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H)
    (F : Conventions.Spec.ContinuousAntidualValue 𝕜 H) (v : H) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (a v v) - RCLike.re (F v)

/-- Both scalar fields, with minimization over the whole space and uniqueness
among all global minimizers. Includes the zero Hilbert space. -/
def LaxMilgram : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H) (α : ℝ),
    Conventions.Spec.FormCoerciveValue 𝕜 H a α →
    ∀ F : Conventions.Spec.ContinuousAntidualValue 𝕜 H,
      ∃ u : H, (∀ v : H, a v u = F v) ∧ ‖u‖ ≤ ‖F‖ / α ∧
        (∀ w : H, (∀ v : H, a v w = F v) → w = u) ∧
        (Conventions.Spec.FormHermitianValue 𝕜 H a →
          (∀ v : H, a v v = (RCLike.re (a v v) : 𝕜)) ∧
          (∀ v : H, energy a F u ≤ energy a F v) ∧
          (∀ w : H, (∀ v : H, energy a F w ≤ energy a F v) → w = u))

/-- Direct real bilinear / real linear version of the complete assertion. -/
def RealLaxMilgram : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (a : H →L[ℝ] H →L[ℝ] ℝ) (α : ℝ),
    0 < α → (∀ v : H, α * ‖v‖ ^ 2 ≤ a v v) →
    ∀ F : H →L[ℝ] ℝ,
      ∃ u : H, (∀ v : H, a v u = F v) ∧ ‖u‖ ≤ ‖F‖ / α ∧
        (∀ w : H, (∀ v : H, a v w = F v) → w = u) ∧
        ((∀ x y : H, a x y = a y x) →
          (∀ v : H, (1 / 2 : ℝ) * a u u - F u ≤ (1 / 2 : ℝ) * a v v - F v) ∧
          (∀ w : H,
            (∀ v : H, (1 / 2 : ℝ) * a w w - F w ≤ (1 / 2 : ℝ) * a v v - F v) →
            w = u))

end ExpandedFA.Hilbert.LaxMilgramEnergy.Spec
