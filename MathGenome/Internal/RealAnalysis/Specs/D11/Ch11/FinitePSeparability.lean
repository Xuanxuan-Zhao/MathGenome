import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.BorelGenerators
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Bases

/-! Independent statements for paper.tex:3805–3826.

The general theorem assumes countable generation of the ORIGINAL sigma-algebra.
The Euclidean conclusion uses the completion of Borel Lebesgue measure, and
imposes no countable-generation assumption on the completed sigma-algebra.
The scalar parameter `RCLike` includes both real and complex scalars.

`SeparableOrdinaryLp` states separability both natively and on the canonical
literal quotient of ordinary measurable functions, with a normed structure
identified by its representative-compatible linear isometry. Thus the source
norm is fixed by the accepted quotient bridge, rather than chosen arbitrarily.
-/
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch11.FinitePSeparability

open Specs.D11.Ch10.QuotientConstruction

/-- Separability on both equivalent realizations of the ordinary a.e. quotient. -/
def SeparableOrdinaryLp {X : Type u} {𝕜 : Type} [m : MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : Prop :=
  SeparableSpace (Lp 𝕜 p μ) ∧
    ∃ G : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p),
    letI := G
    ∃ V : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p),
    letI := V
    ∃ F : QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ,
      (∀ r : Raw (𝕜 := 𝕜) μ p, F (classOf r) = r.property.2.toLp r.val) ∧
      SeparableSpace (QuotientLp (𝕜 := 𝕜) μ p)

/-- The original abstract-space theorem, including arbitrary sigma-finite
positive measures, zero measures and empty spaces. -/
def finite_p_separability : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [MeasurableSpace.CountablyGenerated X]
    (μ : Measure X) [SigmaFinite μ] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    SeparableOrdinaryLp (𝕜 := 𝕜) μ p

/-- Ordinary completion preserves the scalar Lp space isometrically, through
the identity on representatives. No finiteness or countable-generation premise
is needed for this bridge. In the Euclidean application the inverse supplies
a Borel representative of each completed class. -/
def completion_isometry : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ F : Lp 𝕜 p μ ≃ₗᵢ[𝕜] Lp 𝕜 p (Specs.D11.Ch02.Completion.completedMeasure_value μ),
      ∀ f : Lp 𝕜 p μ, (F f : X → 𝕜) =ᵐ[μ] (f : X → 𝕜)

/-- The completed Euclidean Lebesgue conclusion, with the Euclidean l2 space
and its canonical Borel volume, then the ordinary measure completion. -/
def completed_euclidean_separability : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    SeparableOrdinaryLp (𝕜 := 𝕜)
      (m := Specs.D11.Ch02.Completion.completedSpace_value
        (volume : Measure (D11.Ch03.BorelGenerators.Space n)))
      (Specs.D11.Ch02.Completion.completedMeasure_value
        (volume : Measure (D11.Ch03.BorelGenerators.Space n))) p

end Specs.D11.Ch11.FinitePSeparability
