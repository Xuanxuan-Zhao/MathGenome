import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.CohnEndpointTranslation
import MathGenome.Internal.RealAnalysis.D11.Ch20.LocalNullSigmafiniteBridge

/-! Cohn's Chapter 10 convention follows from the full Chapter 20 bridge.
In particular the isometry is onto the ordinary raw-function quotient and
preserves the class of each bounded measurable function. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
universe u
namespace D11.Ch10.CohnEndpointTranslation

open D11.Ch20.LocalNullVariant

theorem locallyNull_iff_null : Specs.D11.Ch10.CohnEndpointTranslation.locallyNull_iff_null :=
  D11.Ch20.LocalNullSigmafiniteBridge.locallyNull_iff_null

theorem classOf_eq_iff_ae : Specs.D11.Ch10.CohnEndpointTranslation.classOf_eq_iff_ae := by
  intro X _ 𝕜 _ μ _ f g
  rw [D11.Ch20.LocalNullVariant.classOf_eq_iff, locallyNull_iff_null]
  have hmeas : MeasurableSet {x | f.val x ≠ g.val x} :=
    (measurableSet_eq_fun f.property.1 g.property.1).compl
  simp only [hmeas, true_and, Filter.EventuallyEq, ae_iff]

theorem endpoint_identification :
    Specs.D11.Ch10.CohnEndpointTranslation.endpoint_identification :=
  D11.Ch20.LocalNullSigmafiniteBridge.quotient_isometry

theorem localNorm_eq_ordinary : Specs.D11.Ch10.CohnEndpointTranslation.localNorm_eq_ordinary := by
  intro X _ 𝕜 _ μ _ f
  obtain ⟨G, V, e, hrep, hnorm⟩ := endpoint_identification (𝕜 := 𝕜) μ
  letI := G
  letI := V
  calc
    LocalNorm μ f = ‖ClassOf μ f‖ := (D11.Ch20.LocalNullVariant.norm_formula μ f).symm
    _ = ‖e (ClassOf μ f)‖ := (e.norm_map _).symm
    _ = ‖Specs.D11.Ch10.QuotientConstruction.classOf
        (Specs.D11.Ch20.LocalNullSigmafiniteBridge.ordinaryRaw μ f)‖ := congrArg norm (hrep f)
    _ = (Specs.D11.Ch04.EssentialBounds.essentialSupNorm_value μ f.val).toReal :=
      hnorm (Specs.D11.Ch20.LocalNullSigmafiniteBridge.ordinaryRaw μ f)

end D11.Ch10.CohnEndpointTranslation
