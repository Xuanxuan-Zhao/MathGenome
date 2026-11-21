import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

/-!
Independent statement of `fa2:p2:banach-analytic` (paper.tex:10074–10077).
An ambient function restricted to an arbitrary open subset represents the function
on that subset. `AnalyticOnNhd` means locally convergent norm power series.
The tests are all continuous complex-linear functionals. No continuity, local
bound, separability, nonemptiness, or nontriviality is assumed.
-/
namespace ExpandedFA.BanachAlgebra.WeakStrongAnalyticity.Spec

universe u

def AnalyticityEquivalence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (U : Set ℂ) (f : ℂ → X), IsOpen U →
    (AnalyticOnNhd ℂ f U ↔
      ∀ ℓ : X →L[ℂ] ℂ, AnalyticOnNhd ℂ (ℓ ∘ f) U)

end ExpandedFA.BanachAlgebra.WeakStrongAnalyticity.Spec
