import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-!
The absolute-diagonal Lax--Milgram theorem, `paper.tex` 7909–7944,
`fa2:p2:absolute-lax-milgram` in `parts/part2-prehilbert-variants.tex`.
The scalar field is real or complex, the test slot is conjugate linear,
and the unknown slot and solution operator are scalar linear. The condition
uses the modulus of the diagonal, not its real part. No symmetry, nonzero
space, dimension, or separability hypothesis is imposed.
-/

namespace ExpandedFA.Hilbert.AbsoluteLaxMilgram.Spec
universe u v

/-- A bounded scalar-linear solution operator on the native continuous
antidual, with existence, uniqueness and both stated quantitative bounds. -/
def AbsoluteLaxMilgram : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H)
    (b : ℝ), 0 < b → (∀ v : H, b * ‖v‖ ^ 2 ≤ ‖a v v‖) →
    ∃ S : Conventions.Spec.ContinuousAntidualValue 𝕜 H →L[𝕜] H,
      ‖S‖ ≤ 1 / b ∧
      ∀ F : Conventions.Spec.ContinuousAntidualValue 𝕜 H,
        (∀ v : H, a v (S F) = F v) ∧
        ‖S F‖ ≤ ‖F‖ / b ∧
        ∀ u : H, (∀ v : H, a v u = F v) → u = S F

end ExpandedFA.Hilbert.AbsoluteLaxMilgram.Spec
