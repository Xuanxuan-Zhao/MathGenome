import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import Mathlib.Topology.MetricSpace.Cauchy

/-! Independent statement for paper.tex:3376–3398.

The carrier is the upstream quotient of ordinarily measurable raw functions.
The normed structures and their representative formulas are conclusions, as in
the upstream construction, so no completeness or representation certificate is
assumed. The exponent includes infinity. The last clause makes the explicitly
adopted infinity endpoint concrete for every choice of raw representatives:
the limit has a bounded measurable representative, and the entire sequence
converges uniformly off one measurable null set in the original sigma-algebra.
No finiteness, sigma-finiteness or completeness of the measure is required.
-/
open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u
noncomputable section
namespace Specs.D11.Ch10.Completeness
open Specs.D11.Ch10.QuotientConstruction

def completeness : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)],
    ∃ G : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p),
    letI := G
    ∃ V : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p),
    letI := V
    ∃ F : QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ,
      (∀ f : Raw (𝕜 := 𝕜) μ p, F (classOf f) = f.property.2.toLp f.val) ∧
      (∀ f : Raw (𝕜 := 𝕜) μ p, ‖classOf f‖ = (sourceNorm μ p f.val).toReal) ∧
      CompleteSpace (QuotientLp (𝕜 := 𝕜) μ p) ∧
      (∀ a : ℕ → QuotientLp (𝕜 := 𝕜) μ p, CauchySeq a →
        ∃! b, Tendsto (fun n => ‖a n - b‖) atTop (𝓝 0)) ∧
      (p = ∞ → ∀ a : ℕ → Raw (𝕜 := 𝕜) μ p,
        CauchySeq (fun n => classOf (a n)) →
        ∃ b : Raw (𝕜 := 𝕜) μ p,
          (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖b.val x‖ ≤ M) ∧
          Tendsto (fun n => classOf (a n)) atTop (𝓝 (classOf b)) ∧
          ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧
            ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ n ≥ k, ∀ x, x ∉ N →
              ‖(a n).val x - b.val x‖ < ε)

end Specs.D11.Ch10.Completeness
