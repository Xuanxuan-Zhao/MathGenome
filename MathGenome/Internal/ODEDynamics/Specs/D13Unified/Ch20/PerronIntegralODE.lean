import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Set MeasureTheory

namespace D13Unified.Ch20.PerronIntegralODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The real-time evolution in the Banach algebra of continuous endomorphisms. -/
def evolution (A : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  NormedSpace.exp (t • A)

/-- The original stable finite integral and unstable improper tail. -/
def stableIntegral (A Ps : E →L[ℝ] E) (g : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, evolution A (t-s) (Ps (g s))

def unstableIntegral (A Pu : E →L[ℝ] E) (g : ℝ → E) (t : ℝ) : E :=
  ∫ s in Ici t, evolution A (t-s) (Pu (g s))

/-- This is the actual Perron formula, in the original, unweighted coordinates. -/
def perronPath (A Ps Pu : E →L[ℝ] E) (g : ℝ → E) (ξ : E) (t : ℝ) : E :=
  evolution A t ξ + stableIntegral A Ps g t - unstableIntegral A Pu g t

end D13Unified.Ch20.PerronIntegralODE

namespace Specs.D13Unified.Ch20.PerronIntegralODE
open _root_.D13Unified.Ch20.PerronIntegralODE
universe u

/-- Linear-forcing bridge on the closed half-line. Integrability concerns the
actual forcing transformed by the inverse evolution, rather than a totalized
integral or an assumed differential identity. -/
def perronIntegralODEType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A Ps Pu : E →L[ℝ] E),
    Ps + Pu = 1 → Ps * Pu = 0 → Commute Ps A → Commute Pu A →
    ∀ (g : ℝ → E), ContinuousOn g (Ici 0) →
    IntegrableOn (fun s => evolution A (-s) (Pu (g s))) (Ici 0) →
    ∀ (ξ : E), Ps ξ = ξ →
    (∀ t : ℝ, 0 ≤ t →
      IntervalIntegrable (fun s => evolution A (t-s) (Ps (g s))) volume 0 t ∧
      IntegrableOn (fun s => evolution A (t-s) (Pu (g s))) (Ici t)) ∧
    ContinuousOn (perronPath A Ps Pu g ξ) (Ici 0) ∧
    (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (perronPath A Ps Pu g ξ)
      (A (perronPath A Ps Pu g ξ t) + g t) (Ici 0) t) ∧
    Ps (perronPath A Ps Pu g ξ 0) = ξ

end Specs.D13Unified.Ch20.PerronIntegralODE
