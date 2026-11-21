import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeakVolterraResolvent
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
Independent statements for the derivative clause of
`fa2:p5:weighted-volterra-regularity`, paper.tex:22332–22338.
The comparison and endpoint expansion clauses have separate allocated goals.
All differentiability is over the real time variable, for either scalar field.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ExpandedFA.PartV.WeightedVolterraDerivatives.Spec
open ExpandedFA.PartV.WeakVolterraBounds.Spec

/-- The original amplitude has a C^m extension to a neighborhood of the
closed triangle. No differentiability of a clamped extension is asserted. -/
def SmoothKernel {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (T : ℝ)
    (k : ℝ × ℝ → 𝕜) : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ triangle T ⊆ U ∧ ContDiffOn ℝ m k U

/-- The equation uses the unnormalized original kernel. Values of the ambient
functions outside [0,T] impose no additional conditions. -/
def IsSolution {𝕜 : Type} [RCLike 𝕜] (α T : ℝ)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
    u t = f t + ζ * ∫ s in Ioc 0 t, (t-s)^(α-1) • (k (t,s) * u s)

/-- Within derivatives retain the left derivative at T, and are unaffected
by arbitrary values of u outside the interval. For T=0 all positive-time
conclusions are vacuous. In particular the subtraction of f is retained. -/
def DerivativeConclusion {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (α T : ℝ)
    (f u : ℝ → 𝕜) : Prop :=
  ContDiffOn ℝ m u (Ioc 0 T) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ m → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Ioc (0 : ℝ) T,
        ‖iteratedDerivWithin j (fun s => u s - f s) (Ioc 0 T) t‖ ≤
          C * t^(α-(j : ℝ))

def WeightedDerivativeRegularity : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (m : ℕ), 0 < α → α < 1 → 0 ≤ T →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜),
      SmoothKernel m T k → ContDiffOn ℝ m f (Icc 0 T) →
      IsSolution α T k f ζ u → DerivativeConclusion m α T f u

/-- Polynomial factors from finite product rules do not require a small
parameter, or a small time interval, in the Gamma-series argument. -/
def PolynomialGammaSummability : Prop := ∀ {α c : ℝ}, 0 < α → 0 ≤ c →
  ∀ d : ℕ, Summable (fun n : ℕ => (n : ℝ)^d * c^n /
    Real.Gamma ((n : ℝ)*α+1))

end ExpandedFA.PartV.WeightedVolterraDerivatives.Spec
