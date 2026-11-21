import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
Independent statements for paper.tex:3609–3622, simple functions of finite
measure support. Scalars may be real or complex (`RCLike`). The measure is
arbitrary, with no finiteness or completeness assumption. `SimpleFunc` has
finite range and measurable fibers; its `Function.support` is precisely its
nonzero set, not its topological support.

The raw formulation uses the previously fixed integral power norm. The native
Lp formulation uses the ordinary a.e. quotient, identified with the source
quotient by the upstream quotient-construction theorem. The final formulation
also asserts density directly on that source quotient, for a normed structure
and isometry satisfying the upstream representative formula.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch11.FinitePSimpleDensity

/-- Approximation of every ordinary measurable raw finite-p function, measured
by the original integral norm. A simple function is zero off its support. -/
def raw_simple_density : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ), 1 ≤ p →
    ∀ f : X → 𝕜, f ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p →
    ∀ ε : ℝ, 0 < ε → ∃ s : SimpleFunc X 𝕜,
      (s : X → 𝕜) ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p ∧
      MeasurableSet (Function.support s) ∧ μ (Function.support s) < ∞ ∧
      Specs.D11.Ch10.LpDefinition.powerNorm_value μ p (f - (s : X → 𝕜)) < ENNReal.ofReal ε

/-- Norm approximation in the native ordinary a.e. quotient. `p ≠ ∞` retains
exactly the finite exponent range; no restriction on the measure is added. -/
def native_simple_density : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)], p ≠ ∞ → ∀ f : Lp 𝕜 p μ, ∀ ε : ℝ, 0 < ε →
    ∃ (s : SimpleFunc X 𝕜) (hs : MemLp s p μ),
      MeasurableSet (Function.support s) ∧ μ (Function.support s) < ∞ ∧
      ‖f - hs.toLp s‖ < ε

open Specs.D11.Ch10.QuotientConstruction

/-- The same density assertion on the literal quotient of ordinary measurable
raw functions. The structures and their representative-compatible isometry
are conclusions, not additional hypotheses on the source space. -/
def finite_p_simple_density : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)], p ≠ ∞ →
    ∃ G : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p),
    letI := G
    ∃ V : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p),
    letI := V
    ∃ F : QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ,
      (∀ r : Raw (𝕜 := 𝕜) μ p, F (classOf r) = r.property.2.toLp r.val) ∧
      ∀ f : QuotientLp (𝕜 := 𝕜) μ p, ∀ ε : ℝ, 0 < ε →
        ∃ (s : SimpleFunc X 𝕜) (hs : MemLp s p μ),
          MeasurableSet (Function.support s) ∧ μ (Function.support s) < ∞ ∧
          ‖f - classOf (⟨s, s.measurable, hs⟩ : Raw (𝕜 := 𝕜) μ p)‖ < ε

end Specs.D11.Ch11.FinitePSimpleDensity
