import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceBoundaryGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurveCovariantDerivative
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open scoped Classical RealInnerProductSpace
namespace P202.Geometry.SurfaceBoundaryGeometry
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open Module
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
universe u
variable {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 a M}

abbrev RegularCurveArc := @P202.SurfaceBoundaryData.RegularArc
abbrev BoundaryCorner := P202.SurfaceBoundaryData.Corner
abbrev inwardUnitNormal := @P202.SurfaceBoundaryData.IsInwardUnitNormal
noncomputable abbrev inwardNormalVector := @P202.SurfaceBoundaryData.normalVector
noncomputable abbrev J := @P202.SurfaceBoundaryData.rotation
noncomputable abbrev positiveBoundaryOrientation := @P202.SurfaceBoundaryData.PositiveBoundaryOrientation
noncomputable abbrev signedGeodesicCurvature := @P202.SurfaceBoundaryData.geodesicCurvature
noncomputable abbrev inwardGeodesicCurvature := @P202.SurfaceBoundaryData.boundaryGeodesicCurvature
noncomputable abbrev geometricBoundaryCurvature := @P202.SurfaceBoundaryData.inwardBoundaryCurvature
noncomputable abbrev smoothArcIntegral := @P202.SurfaceBoundaryData.integralOnArc
noncomputable abbrev piecewiseBoundaryIntegral := @P202.SurfaceBoundaryData.integralOnBoundary
noncomputable abbrev riemannianAreaDensity := @P202.SurfaceBoundaryData.areaDensity
abbrev signedExteriorAngle := P202.SurfaceBoundaryData.exteriorAngle

theorem rotation_properties : P202Specs.Geometry.SurfaceBoundaryGeometry.rotation_propertiesType.{u} := by
  intro a M _ S g o p X Y
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact ⟨(planeOrientation g o p).rightAngleRotation_rightAngleRotation X,
    (planeOrientation g o p).inner_comp_rightAngleRotation X Y,
    (planeOrientation g o p).inner_rightAngleRotation_self X⟩

/-- Coordinates of a determinant vector detect its original positive ray. -/
theorem positive_wedge_iff (p : M) (b : Basis (Fin 2) ℝ (TangentSpace S p))
    (v : Fin 2 → TangentSpace S p) :
    let W := exteriorPower.ιMulti ℝ 2 b
    ∀ hW : W ≠ 0,
      SmoothManifolds.OrientationData.IsPositive (rayOfNeZero ℝ W hW)
        (exteriorPower.ιMulti ℝ 2 v) ↔ 0 < (b.det (R := ℝ) (M := TangentSpace S p)) v := by
  intro W hW
  rw [SmoothManifolds.OrientationResults.positive_iff_pos_smul W hW]
  constructor
  · rintro ⟨t, ht, he⟩
    have hh := congrArg (exteriorPower.alternatingMapLinearEquiv (b.det (R := ℝ) (M := TangentSpace S p))) he
    simp only [W, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      map_smul, Module.Basis.det_self, smul_eq_mul, mul_one] at hh
    exact hh.symm ▸ ht
  · intro hv
    refine ⟨(b.det (R := ℝ) (M := TangentSpace S p)) v, hv, ?_⟩
    dsimp only [W]
    exact @SmoothManifolds.MetricVolumeResults.wedge_basis_expansion
      (TangentSpace S p) inferInstance inferInstance 2 b v

/-- The rotation's algebraic orientation agrees with the original determinant
ray, not merely with an unrelated coordinate orientation. -/
theorem orientation_bridge (g : RiemannianMetric S) (p : M)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (X Y : TangentSpace S p) :
    PositiveBoundaryOrientation o p X Y ↔ 0 < orientedArea g o p X Y := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  change PositiveBoundaryOrientation o p X Y ↔ 0 < (planeOrientation g o p).areaForm X Y
  let b : OrthonormalBasis (Fin 2) ℝ (TangentSpace S p) :=
    (stdOrthonormalBasis ℝ (TangentSpace S p)).reindex
      (finCongr (SmoothManifolds.tangent_dimension S p).2)
  have hb : b.toBasis = referenceBasis g p := rfl
  let W := exteriorPower.ιMulti ℝ 2 b.toBasis
  have hW : W ≠ 0 := by
    intro hz
    have hh := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (b.toBasis.det (R := ℝ) (M := TangentSpace S p)) b.toBasis
    rw [show exteriorPower.ιMulti ℝ 2 b.toBasis = 0 from hz, map_zero,
      Module.Basis.det_self] at hh
    exact zero_ne_one hh
  have hvol : (b.toBasis.orientation (R := ℝ) (M := TangentSpace S p)).volumeForm =
      (b.toBasis.det (R := ℝ) (M := TangentSpace S p)) := Orientation.volumeForm_robust _ b rfl
  have hpos := positive_wedge_iff p b.toBasis ![X, Y] hW
  have hgen : rayOfNeZero ℝ W hW = o.val p ↔
      SmoothManifolds.OrientationData.IsPositive (o.val p) W := by
    constructor
    · intro h; exact ⟨hW, h⟩
    · rintro ⟨_, h⟩; exact h
  by_cases ho : SmoothManifolds.OrientationData.IsPositive (o.val p) W
  · have hr := hgen.mpr ho
    have hp : planeOrientation g o p = b.toBasis.orientation (R := ℝ)
        (M := TangentSpace S p) := by
      simp only [planeOrientation, ← hb]
      exact ite_eq_left ho
    rw [hp, Orientation.areaForm_to_volumeForm, hvol]
    change SmoothManifolds.OrientationData.IsPositive (o.val p) _ ↔ _
    rw [← hr]
    exact hpos
  · have hr : o.val p = -(rayOfNeZero ℝ W hW) := by
      rcases SmoothManifolds.OrientationResults.determinant_ray_eq_or_neg S p
        (o.val p) (rayOfNeZero ℝ W hW) with h | h
      · exact False.elim (ho (hgen.mp h.symm))
      · exact h
    have hp : planeOrientation g o p = -(b.toBasis.orientation (R := ℝ)
        (M := TangentSpace S p)) := by
      simp only [planeOrientation, ← hb]
      exact ite_eq_right ho
    rw [hp, Orientation.areaForm_neg_orientation]
    change SmoothManifolds.OrientationData.IsPositive (o.val p) _ ↔
      0 < -(b.toBasis.orientation (R := ℝ) (M := TangentSpace S p)).areaForm X Y
    rw [Orientation.areaForm_to_volumeForm, hvol, hr, neg_rayOfNeZero]
    rw [SmoothManifolds.OrientationResults.positive_iff_pos_smul (-W) (neg_ne_zero.mpr hW)]
    constructor
    · rintro ⟨t, ht, he⟩
      have hh := congrArg (exteriorPower.alternatingMapLinearEquiv (b.toBasis.det (R := ℝ) (M := TangentSpace S p))) he
      simp only [W, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
        map_smul, map_neg, Module.Basis.det_self, smul_eq_mul, mul_neg, mul_one] at hh
      linarith
    · intro h
      refine ⟨-(b.toBasis.det (R := ℝ) (M := TangentSpace S p)) ![X, Y], h, ?_⟩
      rw [smul_neg, neg_smul, neg_neg]
      exact SmoothManifolds.MetricVolumeResults.wedge_basis_expansion (V := TangentSpace S p) b.toBasis ![X, Y]

theorem rotation_positive : P202Specs.Geometry.SurfaceBoundaryGeometry.rotation_positiveType.{u} := by
  intro a M _ S g o p T ht
  apply (orientation_bridge g p o T (rotation g o p T)).mpr
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  change 0 < (planeOrientation g o p).areaForm T ((planeOrientation g o p).rightAngleRotation T)
  rw [Orientation.areaForm_rightAngleRotation_right]
  exact g.positive p T ht

theorem inward_rotation : P202Specs.Geometry.SurfaceBoundaryGeometry.inward_rotationType.{u} := by
  intro a M _ S g o p ℓ T N hn ht hu hp
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let q := planeOrientation g o p
  have hTT : ⟪T, T⟫ = 1 := hu
  have hNN : ⟪N, N⟫ = 1 := hn.1
  have hNT : ⟪N, T⟫ = 0 := hn.2.1 T ht
  have hTN : ⟪T, N⟫ = 0 := by rw [real_inner_comm]; exact hNT
  have ha : 0 < q.areaForm T N := (orientation_bridge g p o T N).mp hp
  have he := q.inner_sq_add_areaForm_sq T N
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hTT, hNN, hTN] at he
  have ha1 : q.areaForm T N = 1 := by nlinarith
  have hJN : ⟪q.rightAngleRotation T, N⟫ = 1 := by
    rw [q.inner_rightAngleRotation_left, ha1]
  have hNJ : ⟪N, q.rightAngleRotation T⟫ = 1 := by rw [real_inner_comm]; exact hJN
  have hz : ⟪N - q.rightAngleRotation T, N - q.rightAngleRotation T⟫ = 0 := by
    rw [inner_sub_sub_self, hNN, hNJ, hJN, q.inner_comp_rightAngleRotation, hTT]
    norm_num
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp hz)).symm

theorem normalVector_inward :
    P202Specs.Geometry.SurfaceBoundaryGeometry.normalVector_inwardType.{u} := by
  intro a M _ S g p ℓ hℓ
  let e := SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p
  let v := e.symm ℓ
  have hr (w : TangentSpace S p) : pairing g p v w = ℓ w :=
    congrArg (fun f : Module.Dual ℝ (TangentSpace S p) => f w) (e.apply_symm_apply ℓ)
  have hv : v ≠ 0 := by
    intro hz
    apply hℓ
    apply LinearMap.ext
    intro w
    rw [← hr w, hz]
    simp
  have hs : 0 < tangentNorm g p v := Real.sqrt_pos.mpr (g.positive p v hv)
  change IsInwardUnitNormal g p ℓ ((tangentNorm g p v)⁻¹ • v)
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      ← P202.Geometry.SmoothMetrics.tangentNorm_sq g p v]
    field_simp
  · intro w hw
    rw [LinearMap.BilinForm.smul_left, hr, hw, mul_zero]
  · rw [map_smul, smul_eq_mul, ← hr v]
    exact mul_pos (inv_pos.mpr hs) (g.positive p v hv)

theorem boundary_rotation :
    P202Specs.Geometry.SurfaceBoundaryGeometry.boundary_rotationType.{u} := by
  intro a M _ S g o D p b T ht hu hp
  have hn := normalVector_inward g p (scalarDerivative S b.definingFunction p) b.regular
  have he := inward_rotation g o p (scalarDerivative S b.definingFunction p) T
    (boundaryNormal g b) hn ht hu hp
  exact ⟨he, he.symm ▸ hn⟩

theorem unitTangent_unit :
    P202Specs.Geometry.SurfaceBoundaryGeometry.unitTangent_unitType.{u} := by
  intro a M _ S g c t ht
  have hs : 0 < tangentNorm g (c.curve t) (c.velocity t) :=
    Real.sqrt_pos.mpr (g.positive _ _ (c.regular t ⟨ht.1.le, ht.2.le⟩))
  refine ⟨?_, hs⟩
  dsimp only [RegularArc.tangent, unitTangent]
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    ← P202.Geometry.SmoothMetrics.tangentNorm_sq g (c.curve t) (c.velocity t)]
  field_simp

theorem regularArc_derivative :
    P202Specs.Geometry.SurfaceBoundaryGeometry.regularArc_derivativeType.{u} := by
  intro a M _ S g C c t ht
  have hI := Icc_mem_nhds ht.1 ht.2
  have htcc : t ∈ Set.Icc c.left c.right := ⟨ht.1.le, ht.2.le⟩
  obtain ⟨D, V, hV, U, hU, b, hp, v', hv, he⟩ :=
    P202.Geometry.CurveCovariantDerivative.exists_covariantDerivative C htcc
      c.coordinateC1 c.continuous c.unitC1
  refine ⟨D, V, ?_, U, hU, b, hp, v', (hv.hasDerivAt hI).hasDerivWithinAt, he⟩
  obtain ⟨hc, e, he, hp, hd⟩ := hV
  exact ⟨(hc.continuousAt hI).continuousWithinAt,
    e, he, hp, (hd.hasDerivAt hI).hasDerivWithinAt⟩

/-- Reversing both the parameter direction and the unit tangent preserves
D_T T. This uses actual covariant derivatives, including the chain rule. -/
theorem derivative_reverse (C : Connection (tangentBundle S)) (c : ℝ → M)
    (T : (t : ℝ) → TangentSpace S (c t)) (s : ℝ)
    (D : TangentSpace S (c (-s)))
    (hD : P202.CurveConnectionData.HasCovariantDerivativeAt C c T (-s) D) :
    P202.CurveConnectionData.HasCovariantDerivativeAt C (c ∘ Neg.neg)
      (fun t => -T (-t)) s D := by
  have hd := P202.Geometry.CurveCovariantDerivative.ordinary_reparam C hD
    ((hasDerivAt_id s).neg)
  have hh := P202.Geometry.CurveCovariantDerivative.derivative_smul C hd
    (hasDerivAt_const s (-1 : ℝ)).hasDerivWithinAt
  have hn : - -D = D := neg_neg D
  simpa only [zero_smul, zero_add, neg_one_smul, hn] using hh

theorem curvature_reversal :
    P202Specs.Geometry.SurfaceBoundaryGeometry.curvature_reversalType.{u} := by
  intro a M _ S C g c T N speed s D hD
  have hd := derivative_reverse C c T s D hD
  have he := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (Set.mem_univ s) (uniqueDiffWithinAt_univ) hd
  have hf := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (Set.mem_univ (-s)) (uniqueDiffWithinAt_univ) hD
  simp only [inwardCurveCurvature, inwardCurvature, curvatureVector,
    P202.CurveConnectionData.covariantDerivative, he, hf]
  rfl

theorem regularArc_curvature_reversal :
    P202Specs.Geometry.SurfaceBoundaryGeometry.regularArc_curvature_reversalType.{u} := by
  intro a M _ S C g hC c N s hs
  refine ⟨?_, ?_⟩
  · have hn : (-1 : ℝ) • c.velocity (-s) = -c.velocity (-s) :=
      neg_one_smul ℝ (M := TangentSpace S (c.curve (-s))) (c.velocity (-s))
    simpa only [hn] using
      P202.Geometry.PiecewiseCurves.HasVelocityAt.reparam (c.hasVelocity (-s) hs)
        ((hasDerivAt_id s).neg)
  · have hT : unitTangent g (c.curve ∘ Neg.neg) (fun t => -c.velocity (-t)) =
        (fun t => -c.tangent (-t)) := by
      funext t
      dsimp [unitTangent, RegularArc.tangent]
      rw [P202.Geometry.SmoothMetrics.tangentNorm_neg]
      exact smul_neg ((tangentNorm g (c.curve (-t)) (c.velocity (-t)))⁻¹) (c.velocity (-t))
    have hv : (fun t => tangentNorm g (c.curve (-t)) (-c.velocity (-t))) =
        (fun t => c.speed (-t)) := by
      funext t
      exact P202.Geometry.SmoothMetrics.tangentNorm_neg g (c.curve (-t)) (c.velocity (-t))
    rw [hT, hv]
    obtain ⟨D, hd⟩ := regularArc_derivative g C c (-s) hs
    exact curvature_reversal C g c.curve c.tangent N c.speed s D hd

theorem geometricBoundary_normal :
    P202Specs.Geometry.SurfaceBoundaryGeometry.geometricBoundary_normalType.{u} := by
  intro a M _ S g D p b
  exact normalVector_inward g p (scalarDerivative S b.definingFunction p) b.regular

theorem geometricBoundary_reversal :
    P202Specs.Geometry.SurfaceBoundaryGeometry.geometricBoundary_reversalType.{u} := by
  intro a M _ S C g hC c D s b hs
  have hT : unitTangent g (c.curve ∘ Neg.neg) (fun t => -c.velocity (-t)) =
      (fun t => -c.tangent (-t)) := by
    funext t
    dsimp [unitTangent, RegularArc.tangent]
    rw [P202.Geometry.SmoothMetrics.tangentNorm_neg]
    exact smul_neg ((tangentNorm g (c.curve (-t)) (c.velocity (-t)))⁻¹) (c.velocity (-t))
  have hv : (fun t => tangentNorm g (c.curve (-t)) (-c.velocity (-t))) =
      (fun t => c.speed (-t)) := by
    funext t
    exact P202.Geometry.SmoothMetrics.tangentNorm_neg g (c.curve (-t)) (c.velocity (-t))
  rw [hT, hv]
  obtain ⟨A, hA⟩ := regularArc_derivative g C c (-s) hs
  have hr := derivative_reverse C c.curve c.tangent s A hA
  have he := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (Set.mem_univ s) uniqueDiffWithinAt_univ hr
  have hf := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (Set.mem_univ (-s)) uniqueDiffWithinAt_univ hA
  simp only [inwardBoundaryCurvature, inwardCurvature, curvatureVector,
    P202.CurveConnectionData.covariantDerivative, he, hf]

theorem signed_inward : P202Specs.Geometry.SurfaceBoundaryGeometry.signed_inwardType.{u} := by
  intro a M _ S g o p ℓ T N A hn ht hu hp
  unfold signedCurvature inwardCurvature
  rw [inward_rotation g o p ℓ T N hn ht hu hp]

theorem area_compatible : P202Specs.Geometry.SurfaceBoundaryGeometry.area_compatibleType.{u} := by
  intro a M _ S g
  exact ⟨(P202.Geometry.RiemannianVolume.density_properties g).1,
    (P202.Geometry.RiemannianVolume.density_properties g).2.1,
    fun o => (P202.Geometry.RiemannianVolume.volumeForm_properties g o).2.1⟩

theorem corners : P202Specs.Geometry.SurfaceBoundaryGeometry.cornersType := by
  refine ⟨?_, ?_, ?_⟩
  · intro c; dsimp [exteriorAngle]; constructor <;> linarith [c.positive, c.less_two_pi]
  · intro c h; dsimp [exteriorAngle]; linarith
  · intro c h; simp [exteriorAngle, h]
end P202.Geometry.SurfaceBoundaryGeometry
