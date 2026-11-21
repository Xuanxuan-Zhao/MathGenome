import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullVariant
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction

/-! Independent statements for paper.tex:5762–5770, also the endpoint
translation at the end of Chapter 10. All measures use the original specified
sigma-algebra. Local nullity includes measurability, as in the source.
The representative formula fixes the quotient identification, rather than
merely asserting an abstract isometry between two spaces.
-/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
universe u
namespace Specs.D11.Ch20.LocalNullSigmafiniteBridge

open _root_.D11.Ch20.LocalNullVariant

/-- The ordinary quotient projection of a bounded measurable representative. -/
theorem ordinaryMemLp {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) (f : BoundedMeasurable X 𝕜) : MemLp f.val ∞ μ := by
  obtain ⟨C, _, hC⟩ := f.property.2
  exact memLp_top_of_bound f.property.1.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

def ordinaryRaw {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) (f : BoundedMeasurable X 𝕜) : Specs.D11.Ch10.QuotientConstruction.Raw (𝕜 := 𝕜) μ ∞ :=
  ⟨f.val, f.property.1, ordinaryMemLp μ f⟩

def null_locallyNull : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (N : Set X),
    MeasurableSet N → μ N = 0 → LocallyNull μ N

def locallyNull_iff_null : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (N : Set X),
    LocallyNull μ N ↔ MeasurableSet N ∧ μ N = 0

/-- Native Lp is the previously verified model of the ordinary measurable
a.e. quotient; this formula identifies the same bounded function on both sides. -/
def native_isometry : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ],
    ∃ e : LocalLInfinity 𝕜 μ ≃ₗᵢ[𝕜] Lp 𝕜 ∞ μ,
      ∀ f : BoundedMeasurable X 𝕜,
        e (ClassOf μ f) = (ordinaryMemLp μ f).toLp f.val

/-- An explicit identification with the original raw-function quotient too.
The norm on every ordinary raw class is required to be its source essential
norm, so the existential structures cannot change the ordinary quotient norm. -/
def quotient_isometry : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ],
    ∃ G : NormedAddCommGroup (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞),
    letI := G
    ∃ V : NormedSpace 𝕜 (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞),
    letI := V
    ∃ e : LocalLInfinity 𝕜 μ ≃ₗᵢ[𝕜] Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞,
      (∀ f : BoundedMeasurable X 𝕜,
        e (ClassOf μ f) = Specs.D11.Ch10.QuotientConstruction.classOf (ordinaryRaw μ f)) ∧
      (∀ f : Specs.D11.Ch10.QuotientConstruction.Raw (𝕜 := 𝕜) μ ∞,
        ‖Specs.D11.Ch10.QuotientConstruction.classOf f‖ = (Specs.D11.Ch10.QuotientConstruction.sourceNorm μ ∞ f.val).toReal)

end Specs.D11.Ch20.LocalNullSigmafiniteBridge
