import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ProximalExistence
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function

/-! Independent statements for the convexity, Fréchet derivative, and exact
Lipschitz estimate in paper.tex, Theorem `thm:moreau` (1276–1281, 1290–1307).
The real representative is tied to the actual extended-real infimum, so
`toReal`'s values at infinity play no role under the stated hypotheses. -/
noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def realMoreauEnvelopeType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → WithTop ℝ) → ℝ → H → ℝ

def realMoreauEnvelope : realMoreauEnvelopeType.{u} :=
  fun f μ x => (moreauEnvelope f μ x).toReal

def moreauGradientType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → WithTop ℝ) → ℝ → H → H

def moreauGradient : moreauGradientType.{u} :=
  fun f μ x => μ⁻¹ • (x - proximalMap f μ x)

def realMoreauEnvelope_coe : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H,
      moreauEnvelope f μ x = (realMoreauEnvelope f μ x : EReal)

def realMoreauEnvelope_convex : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ConvexOn ℝ Set.univ (realMoreauEnvelope f μ)

def realMoreauEnvelope_hasFDerivAt : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H,
      HasFDerivAt (realMoreauEnvelope f μ)
        (InnerProductSpace.toDual ℝ H (moreauGradient f μ x)) x

def moreauGradient_lipschitz : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x y : H,
      ‖moreauGradient f μ x - moreauGradient f μ y‖ ≤ ‖x - y‖ / μ

end VariationalNotes.ConvexAnalysis.Specs
