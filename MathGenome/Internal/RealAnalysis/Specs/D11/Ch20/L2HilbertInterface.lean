import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Independent specification of paper.tex:5671–5679.

The carrier is the upstream ordinary quotient of measurable scalar functions,
on the specified original measurable space. The structures are conclusions.
The isometry's representative formula fixes both the vector operations and norm.
Lean's inner product is linear in its second argument, so the paper's first-slot
pairing is `inner 𝕜 g f`. Its representative formula below includes a proof of
absolute integrability before evaluation of the shared scalar integral.
No sigma-finiteness, completeness of the measure, or separability is assumed.
-/
open MeasureTheory
open scoped ENNReal ComplexConjugate
universe u
noncomputable section
namespace Specs.D11.Ch20.L2HilbertInterface
open Specs.D11.Ch10.QuotientConstruction
open Specs.D11.Ch06.ScalarIntegral

/-- The full Hilbert-space assertion, retaining the source's first-slot convention. -/
def l2_hilbert : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X),
    ∃ G : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ 2),
    letI := G
    ∃ H : InnerProductSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ 2),
    letI := H
    ∃ F : QuotientLp (𝕜 := 𝕜) μ 2 ≃ₗᵢ[𝕜] Lp 𝕜 2 μ,
      (∀ f : Raw (𝕜 := 𝕜) μ 2, F (classOf f) = f.property.2.toLp f.val) ∧
      (∀ f : Raw (𝕜 := 𝕜) μ 2, ‖classOf f‖ = (sourceNorm μ 2 f.val).toReal) ∧
      CompleteSpace (QuotientLp (𝕜 := 𝕜) μ 2) ∧
      (∀ f g : Raw (𝕜 := 𝕜) μ 2,
        ∃ h : scalarIntegrable_value μ (fun x => f.val x * conj (g.val x)),
          inner 𝕜 (classOf g) (classOf f) =
            scalarIntegral_value μ (fun x => f.val x * conj (g.val x)) h) ∧
      (∀ f g h : QuotientLp (𝕜 := 𝕜) μ 2,
        inner 𝕜 h (f + g) = inner 𝕜 h f + inner 𝕜 h g) ∧
      (∀ (c : 𝕜) (f g : QuotientLp (𝕜 := 𝕜) μ 2),
        inner 𝕜 g (c • f) = c * inner 𝕜 g f) ∧
      (∀ f g : QuotientLp (𝕜 := 𝕜) μ 2,
        inner 𝕜 f g = conj (inner 𝕜 g f)) ∧
      (∀ f : QuotientLp (𝕜 := 𝕜) μ 2,
        inner 𝕜 f f = (‖f‖ : 𝕜) ^ 2 ∧ (inner 𝕜 f f = 0 ↔ f = 0)) ∧
      (∀ f g : QuotientLp (𝕜 := 𝕜) μ 2,
        ‖inner 𝕜 g f‖ ≤ ‖f‖ * ‖g‖)

end Specs.D11.Ch20.L2HilbertInterface
