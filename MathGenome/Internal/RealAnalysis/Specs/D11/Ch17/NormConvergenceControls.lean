import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
Independent statements for paper.tex:5254–5263. `Lp` is the ordinary a.e.
quotient, identified with the source quotient by the upstream quotient
construction. Convergence below uses its norm topology. The conclusions hold
for every choice of ordinary measurable representatives, with a separate a.e.
equality for each member. No finiteness assumption is imposed on the measure.
-/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace Specs.D11.Ch17.NormConvergenceControls
open Specs.D11.Ch17.UniformControls

/-- All real finite exponents at least one, including the endpoint one.
The power densities have both integral controls and a uniform L1 bound;
the original quotient norms are also bounded. -/
def lp_norm_convergence_controls : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (hp : 1 ≤ p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∀ (F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ) (f : Lp 𝕜 (ENNReal.ofReal p) μ)
      (G : ℕ → X → 𝕜),
      (∀ n, Measurable (G n)) → (∀ n, G n =ᵐ[μ] (F n)) →
      Tendsto F atTop (𝓝 f) →
      lpUiSmall_value μ p G ∧ lpSpatialTails_value μ p G ∧
        lpUniformL1Bound_value μ p G ∧ ∃ C : ℝ, ∀ n, ‖F n‖ ≤ C

/-- The L1 conclusion concerns the representatives themselves, rather than
only their nonnegative absolute-value densities. -/
def l1_norm_convergence_controls : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (F : ℕ → Lp 𝕜 1 μ) (f : Lp 𝕜 1 μ) (G : ℕ → X → 𝕜),
    (∀ n, Measurable (G n)) → (∀ n, G n =ᵐ[μ] (F n)) →
    Tendsto F atTop (𝓝 f) →
    uiSmall_value μ G ∧ spatialTails_value μ G ∧
      uniformL1Bound_value μ G ∧ ∃ C : ℝ, ∀ n, ‖F n‖ ≤ C

end Specs.D11.Ch17.NormConvergenceControls
