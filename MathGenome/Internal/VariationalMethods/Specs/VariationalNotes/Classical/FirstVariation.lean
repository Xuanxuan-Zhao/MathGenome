import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.VariationSpaces
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.DistributionalPrimitive
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace VariationalNotes.Classical

/-- The usual first-variation density, with independent state and velocity fields. -/
def variationDensity {m : ℕ} (p q η θ : ℝ → State m) (t : ℝ) : ℝ :=
  inner ℝ (q t) (η t) + inner ℝ (p t) (θ t)

/-- Momentum and state gradient extended outside the closed reference interval.
Only their values in the interval are used in the statements below. -/
def momentumField {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m) :
    ℝ → State m := fun t =>
  if ht : t ∈ Icc I.a I.b then momentum L u ⟨t, ht⟩ else 0

def stateGradientField {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m) :
    ℝ → State m := fun t =>
  if ht : t ∈ Icc I.a I.b then stateGradient L u ⟨t, ht⟩ else 0

/-- Directional integrands need no classical regularity in time. The measurability
clause makes the nearby energies ordinary Lebesgue integrals, as in the source.
No integrability or continuity of p and q is imposed separately. -/
def DominatedDirection (I : Interval) (F : ℝ → ℝ → ℝ) (D : ℝ → ℝ) : Prop :=
  (∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable (F s) (volume.restrict (Ioo I.a I.b))) ∧
  ∃ r > 0, ∃ B : ℝ → ℝ, IntegrableOn B (Ioo I.a I.b) ∧
    ∃ F' : ℝ → ℝ → ℝ,
      (∀ᵐ t ∂volume.restrict (Ioo I.a I.b), F' 0 t = D t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo I.a I.b), ∀ s ∈ Metric.ball (0 : ℝ) r,
        HasDerivAt (fun s => F s t) (F' s t) s ∧ ‖F' s t‖ ≤ B t)

end VariationalNotes.Classical

namespace Specs.VariationalNotes.Classical.FirstVariation
open _root_.VariationalNotes.Classical

/-- Differentiation of the classical action, before using minimality. -/
def classicalActionDerivative : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u η : C1Curve I m),
    regularNearGraph L u 1 →
    HasDerivAt (fun s : ℝ => action L (u + s • η))
      (∫ t in I.a..I.b, variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t) 0

def classicalFirstVariation : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m),
    (weakLocalMinimum L xₐ xᵦ u ∨ strongLocalMinimum L xₐ xᵦ u) →
    regularNearGraph L u 1 →
    ∀ η : C1Curve I m, η ∈ endpointZero I m →
      HasDerivAt (fun s : ℝ => action L (u + s • η))
        (∫ t in I.a..I.b, variationDensity (momentumField L u) (stateGradientField L u)
          (stateField I m η) (velocityField I m η) t) 0 ∧
      (∫ t in I.a..I.b, variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t) = 0

/-- Distributional and classical conclusions concern the open interval only. -/
def classicalEulerLagrange : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m),
    (weakLocalMinimum L xₐ xᵦ u ∨ strongLocalMinimum L xₐ xᵦ u) →
    regularNearGraph L u 1 →
    WeakDerivativeInterval m I.a I.b (momentumField L u) (stateGradientField L u) ∧
    ContDiffOn ℝ 1 (momentumField L u) (Ioo I.a I.b) ∧
    (∀ t ∈ Ioo I.a I.b,
      HasDerivAt (momentumField L u) (stateGradientField L u t) t)

/-- The finite-energy version for smooth interior tests. Here v is the supplied
velocity field of the underlying curve; the argument only uses the tested
integrands and so does not need any additional time regularity of u or v. -/
def dominatedFirstVariation : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : (ℝ × State m × State m) → ℝ)
    (u v p q : ℝ → State m),
    IntegrableOn (fun t => L (t, u t, v t)) (Ioo I.a I.b) →
    (∀ η : ℝ → State m, smoothInteriorTest I η →
      IsLocalMin (fun s : ℝ => ∫ t in Ioo I.a I.b,
        L (t, u t + s • η t, v t + s • deriv η t)) 0) →
    (∀ η : ℝ → State m, smoothInteriorTest I η →
      DominatedDirection I
        (fun s t => L (t, u t + s • η t, v t + s • deriv η t))
        (variationDensity p q η (deriv η))) →
    ∀ η : ℝ → State m, smoothInteriorTest I η →
      IntegrableOn (variationDensity p q η (deriv η)) (Ioo I.a I.b) ∧
      HasDerivAt (fun s : ℝ => ∫ t in Ioo I.a I.b,
        L (t, u t + s • η t, v t + s • deriv η t))
        (∫ t in Ioo I.a I.b, variationDensity p q η (deriv η) t) 0 ∧
      (∫ t in Ioo I.a I.b, variationDensity p q η (deriv η) t) = 0

end Specs.VariationalNotes.Classical.FirstVariation
