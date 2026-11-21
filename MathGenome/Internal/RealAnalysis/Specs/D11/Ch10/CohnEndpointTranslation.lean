import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullSigmafiniteBridge

/-! The Chapter 10 endpoint convention (paper.tex:3584–3598).
All carriers, null predicates and norms are the canonical shared objects.
The ordinary quotient uses measurable functions on the original sigma-algebra;
no completion or finiteness of total mass is assumed. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
universe u
namespace Specs.D11.Ch10.CohnEndpointTranslation

open _root_.D11.Ch20.LocalNullVariant

/-- Local and ordinary nullity coincide on measurable sets in a sigma-finite space. -/
def locallyNull_iff_null : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (N : Set X),
    LocallyNull μ N ↔ MeasurableSet N ∧ μ N = 0

/-- The two equivalence relations agree on bounded measurable representatives. -/
def classOf_eq_iff_ae : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f g : BoundedMeasurable X 𝕜),
    ClassOf μ f = ClassOf μ g ↔ f.val =ᵐ[μ] g.val

/-- The local essential norm equals the original ordinary essential norm. -/
def localNorm_eq_ordinary : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : BoundedMeasurable X 𝕜),
    LocalNorm μ f = (Specs.D11.Ch04.EssentialBounds.essentialSupNorm_value μ f.val).toReal

/-- A full linear isometric identification with the literal Chapter 10 raw
quotient. The formula on representatives fixes the map, and the last clause
fixes its ordinary quotient norm to the source essential norm. -/
def endpoint_identification : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ],
    ∃ G : NormedAddCommGroup (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞),
    letI := G
    ∃ V : NormedSpace 𝕜 (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞),
    letI := V
    ∃ e : LocalLInfinity 𝕜 μ ≃ₗᵢ[𝕜] Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞,
      (∀ f : BoundedMeasurable X 𝕜,
        e (ClassOf μ f) = Specs.D11.Ch10.QuotientConstruction.classOf
          (Specs.D11.Ch20.LocalNullSigmafiniteBridge.ordinaryRaw μ f)) ∧
      (∀ f : Specs.D11.Ch10.QuotientConstruction.Raw (𝕜 := 𝕜) μ ∞,
        ‖Specs.D11.Ch10.QuotientConstruction.classOf f‖ =
          (Specs.D11.Ch10.QuotientConstruction.sourceNorm μ ∞ f.val).toReal)

end Specs.D11.Ch10.CohnEndpointTranslation
