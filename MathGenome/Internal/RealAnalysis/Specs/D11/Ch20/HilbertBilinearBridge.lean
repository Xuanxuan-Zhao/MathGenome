import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.L2HilbertInterface
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing

/-! Independent specification of paper.tex:5698–5703.

All structures and maps below are conclusions on the ordinary measurable a.e.
quotient, with its source norm. Reversal of Lean's inner-product arguments is
exactly the paper's first-slot-linear convention. The two assignments are
bundled isometric equivalences: the Hilbert assignment is conjugate-linear,
whereas the bilinear density assignment is scalar-linear. Their representative
formulas include absolute integrability on the original measurable space.
-/
open MeasureTheory
open scoped ENNReal ComplexConjugate
universe u
noncomputable section
namespace Specs.D11.Ch20.HilbertBilinearBridge
open Specs.D11.Ch10.QuotientConstruction
open Specs.D11.Ch06.ScalarIntegral

def hilbert_bilinear_bridge : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X),
    ∃ N : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ 2), letI := N
    ∃ I : InnerProductSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ 2), letI := I
    ∃ F : QuotientLp (𝕜 := 𝕜) μ 2 ≃ₗᵢ[𝕜] Lp 𝕜 2 μ,
    ∃ C : QuotientLp (𝕜 := 𝕜) μ 2 ≃ₗᵢ⋆[𝕜] QuotientLp (𝕜 := 𝕜) μ 2,
    ∃ H : (QuotientLp (𝕜 := 𝕜) μ 2 →L[𝕜] 𝕜) ≃ₗᵢ⋆[𝕜]
      QuotientLp (𝕜 := 𝕜) μ 2,
    ∃ G : (QuotientLp (𝕜 := 𝕜) μ 2 →L[𝕜] 𝕜) ≃ₗᵢ[𝕜]
      QuotientLp (𝕜 := 𝕜) μ 2,
    ∃ B : QuotientLp (𝕜 := 𝕜) μ 2 →L[𝕜]
      QuotientLp (𝕜 := 𝕜) μ 2 →L[𝕜] 𝕜,
      (∀ f : Raw (𝕜 := 𝕜) μ 2, F (classOf f) = f.property.2.toLp f.val) ∧
      (∀ f : Raw (𝕜 := 𝕜) μ 2, ‖classOf f‖ = (sourceNorm μ 2 f.val).toReal) ∧
      CompleteSpace (QuotientLp (𝕜 := 𝕜) μ 2) ∧
      (∀ f : Raw (𝕜 := 𝕜) μ 2,
        ∃ hc : Measurable (fun x => conj (f.val x)) ∧
            MemLp (fun x => conj (f.val x)) 2 μ,
          C (classOf f) = classOf ⟨fun x => conj (f.val x), hc⟩) ∧
      (∀ f, C (C f) = f) ∧
      (∀ f g : Raw (𝕜 := 𝕜) μ 2,
        ∃ hi : scalarIntegrable_value μ (fun x => f.val x * conj (g.val x)),
          inner 𝕜 (classOf g) (classOf f) =
            scalarIntegral_value μ (fun x => f.val x * conj (g.val x)) hi) ∧
      (∀ f g : Raw (𝕜 := 𝕜) μ 2,
        ∃ hi : scalarIntegrable_value μ (fun x => f.val x * g.val x),
          B (classOf g) (classOf f) =
            scalarIntegral_value μ (fun x => f.val x * g.val x) hi) ∧
      (∀ ℓ, G ℓ = C (H ℓ)) ∧
      (∀ ℓ f, ℓ f = inner 𝕜 (H ℓ) f ∧ ℓ f = B (G ℓ) f) ∧
      (∀ ℓ, ‖H ℓ‖ = ‖ℓ‖ ∧ ‖G ℓ‖ = ‖ℓ‖) ∧
      (∀ ℓ h, (∀ f, ℓ f = inner 𝕜 h f) → h = H ℓ) ∧
      (∀ ℓ g, (∀ f, ℓ f = B g f) → g = G ℓ)

end Specs.D11.Ch20.HilbertBilinearBridge
