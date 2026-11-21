import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.WeakImmersion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.ProperWhitney
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.GoodProjections

namespace SmoothManifolds.WeakImmersion
open ModelData AtlasData FiniteRegularityData GoodProjectionData
universe u

/-- Weak Whitney immersion in exactly `2 * n` dimensions, including ordinary
boundary, empty manifolds and dimension zero. -/
theorem exists_immersion :
    Specs.SmoothManifolds.Ch04.WeakImmersion.exists_immersionType.{u} := by
  classical
  intro n a M _ S
  obtain ⟨e, he, _, _, _⟩ := ProperWhitney.exists_proper_embedding S
  let : Nonempty (ProjectiveData.RealProjectiveSpace (2 * n)) :=
    ⟨ProjectiveData.projectiveProjection (SphereTorus.sphereBase (2 * n))⟩
  obtain ⟨L, _, hL⟩ :=
    (GoodProjections.immersion_directions_dense S e he (by omega) ⊥ bot_ne_top).nonempty
  -- Identify the actual projection range with the desired Euclidean target.
  let A : ProjectionSpace L ≃L[ℝ] Euclidean (2 * n) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [GoodProjections.projectionSpace_finrank]
      simp [Euclidean, ModelData.Euclidean])
  let R : Euclidean (2 * n + 1) →L[ℝ] ProjectionSpace L :=
    (projectionLinear L).rangeRestrict.toContinuousLinearMap
  let P : Euclidean (2 * n + 1) →L[ℝ] Euclidean (2 * n) :=
    A.toContinuousLinearMap.comp R
  have hP (z w : Euclidean (2 * n + 1)) (h : P z = P w) :
      projection L z = projection L w :=
    congrArg Subtype.val (A.injective h)
  refine ⟨fun p => P (e p), GoodProjections.smoothEuclidean_postcomp S e he.1 P, ?_⟩
  intro c hc p hp v w hvw
  apply hL.2 c hc p hp
  change coordinateDerivative c (fun x => projection L (e x)) p v =
    coordinateDerivative c (fun x => projection L (e x)) p w
  rw [GoodProjections.coordinateDerivative_postcomp c e p hp
    ((he.1 p).2 c hc hp)] at hvw ⊢
  exact hP _ _ hvw

end SmoothManifolds.WeakImmersion
