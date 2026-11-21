import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionCalculus
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.InducedConnections
import Mathlib.Analysis.Calculus.MeanValue
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalFlow

/-! Theorem 6.5: the intrinsic geodesic spray, its actual maximal flow domains,
affine reparametrization, and constant speed for Levi–Civita geodesics. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.GeodesicIVP
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.GeodesicData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Chain rule for velocity and two applications of linearity give the square
of the scale factor in the acceleration. This also covers zero scale. -/
theorem geodesic_affine (C : Connection (tangentBundle S))
    {I : Set ℝ} {q : ℝ → Phase S} (a b : ℝ) (hq : IsGeodesicOn S C I q) :
    IsGeodesicOn S C (affineDomain I a b) (affineCurve S q a b) := by
  intro t ht
  obtain ⟨hv, hD⟩ := hq (a * t + b) ht
  have hφ : HasDerivAt (fun s : ℝ => a * s + b) a t := by
    simpa using ((hasDerivAt_id t).const_mul a).add_const b
  refine ⟨?_, ?_⟩
  · exact CurveCovariantDerivative.velocity_reparam (φ := fun s => a * s + b) (s := t) hv hφ.hasDerivWithinAt
      (mapsTo_univ _ _)
  · have hcomp := CurveCovariantDerivative.ordinary_reparam C (φ := fun s => a * s + b) (s := t) hD hφ
    have hscale := CurveCovariantDerivative.derivative_const_smul C hcomp a
    convert hscale using 1 <;> simp only [affineCurve, Function.comp_def, smul_zero]

/-- No differential equation theorem is needed to compare two curves that
already satisfy the full universal maximality property. -/
theorem maximal_unique_of_universal_property (C : Connection (tangentBundle S))
    {w : Phase S} {I J : D13Unified.OpenTimeInterval} {q r : ℝ → Phase S}
    (hq : IsMaximalThrough S C w I q) (hr : IsMaximalThrough S C w J r) :
    I.carrier = J.carrier ∧ EqOn q r I.carrier := by
  have hJI := hq.2.2.2 J r hr.1 hr.2.1 hr.2.2.1
  have hIJ := hr.2.2.2 I q hq.1 hq.2.1 hq.2.2.1
  exact ⟨Subset.antisymm hIJ.1 hJI.1, fun _ ht => (hIJ.2 ht).symm⟩

/-- The zero vector really gives zero covariant acceleration, for every
connection, in the actual tangent fibers. -/
theorem constant_is_geodesic (C : Connection (tangentBundle S)) (p : M) :
    IsGeodesicOn S C univ (constantCurve S p) := by
  dsimp only [IsGeodesicOn, constantCurve]
  intro t _
  have hv : HasVelocityWithinAt S (fun _ : ℝ => p) univ t 0 := by
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    refine ⟨continuousWithinAt_const, e, he, hp, ?_⟩
    simpa only [map_zero] using hasDerivWithinAt_const t univ (e p).val
  refine ⟨hv, ?_⟩
  obtain ⟨U, hU, hp, ⟨b⟩⟩ :=
    SmoothManifolds.ConstantRankBundles.exists_localFrame (tangentBundle S) p
  have hc : coefficientsAlong b (fun _ : ℝ => p) (fun _ => 0) = fun _ => 0 := by
    funext s
    simp [coefficientsAlong, hp]
  refine ⟨0, hv, U, hU, b, hp, 0, ?_, ?_⟩
  · rw [hc]
    exact hasDerivWithinAt_const t univ 0
  · simp only [frameDerivative, hc, Matrix.mulVec_zero, add_zero, map_zero]

/-- The local vector equation v' + Γ(γ')v = 0 is equivalent to vanishing
covariant acceleration whenever the specified velocity is the actual velocity.
It is an equality in the original fiber, without an assumed ODE solution. -/
theorem covariant_acceleration_eq_zero_iff
    (C : Connection (tangentBundle S))
    {c : ℝ → M} {V : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hV : HasVelocityWithinAt S c univ t (V t))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hp : c t ∈ U) {v' : Euclidean n}
    (hv : HasDerivAt (coefficientsAlong b c V) v' t) :
    HasCovariantDerivativeAt C c V t 0 ↔
      v' + (connectionMatrix C b ⟨c t, hp⟩ (V t)).mulVec
        (coefficientsAlong b c V t) = 0 := by
  constructor
  · intro hD
    have heq := CurveCovariantDerivative.local_formula C (mem_univ t)
      (uniqueDiffWithinAt_univ) hD b hp hV hv.hasDerivWithinAt
    have h := congrArg (b.basis ⟨c t, hp⟩).equivFun heq
    simpa only [map_zero, frameDerivative, LinearEquiv.apply_symm_apply] using h.symm
  · intro heq
    refine ⟨V t, hV, U, hU, b, hp, v', hv.hasDerivWithinAt, ?_⟩
    simp only [frameDerivative, heq, map_zero]

/-- The frame equation is available in every frame, not just the witness
frame occurring in the definition of covariant differentiation. -/
theorem geodesic_frame_equation (C : Connection (tangentBundle S))
    {I : Set ℝ} {q : ℝ → Phase S} (hq : IsGeodesicOn S C I q)
    {t : ℝ} (ht : t ∈ I)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hp : (q t).1 ∈ U) :
    HasDerivAt (coefficientsAlong b (fun s => (q s).1) (fun s => (q s).2))
      (- (connectionMatrix C b ⟨(q t).1, hp⟩ (q t).2).mulVec
        (coefficientsAlong b (fun s => (q s).1) (fun s => (q s).2) t)) t := by
  obtain ⟨v', hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv C
    (mem_univ t) (hq t ht).2 b hp
  rw [hasDerivWithinAt_univ] at hv
  have heq := (covariant_acceleration_eq_zero_iff C (hq t ht).1 b hp hv).mp (hq t ht).2
  have heq' := eq_neg_of_add_eq_zero_left heq
  rwa [← heq']

/-- The vector in the frozen coordinate definition is exactly the member of
its actual trivialization frame. -/
theorem coordinateVector_eq_frame
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (j : Fin n) :
    P202.LeviCivitaData.coordinateVector c j p.val =
      (SmoothManifolds.ConstantRankBundles.trivializationFrame
        (tangentBundle S) c).basis p j := by
  change _ = ((tangentBundle S).fiberCoordinates c p.val p.property).symm
    ((Pi.basisFun ℝ (Fin n)) j)
  rw [Pi.basisFun_apply]
  rfl

/-- Linearity in the tangent argument expands Γ(v)v into the required
quadratic Christoffel expression. This is valid also in dimension zero. -/
theorem coordinateAcceleration_eq_matrix
    (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    let w := (b.basis p).equivFun v
    coordinateAcceleration S C c p w = - (connectionMatrix C b p v).mulVec w := by
  classical
  dsimp only
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let w := (b.basis p).equivFun v
  have hlinear (k j : Fin n) :
      connectionForm C b p k j v = ∑ i : Fin n,
        w i * P202.LeviCivitaData.christoffel C c p k i j := by
    conv_lhs => rw [← (b.basis p).sum_equivFun v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change _ = w i * connectionForm C b p k j
      (P202.LeviCivitaData.coordinateVector c i p.val)
    rw [coordinateVector_eq_frame]
    rfl
  change coordinateAcceleration S C c p w = - (connectionMatrix C b p v).mulVec w
  ext k
  simp only [coordinateAcceleration, Pi.neg_apply, Matrix.mulVec, dotProduct,
    connectionMatrix, hlinear, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The frame coordinates are the fixed intrinsic tangent coordinates. -/
theorem trivializationFrame_equivFun
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) c).basis p).equivFun v =
      (tangentBundle S).fiberCoordinates c p.val p.property v := by
  change ((Pi.basisFun ℝ (Fin n)).map
    ((tangentBundle S).fiberCoordinates c p.val p.property).symm).equivFun v = _
  rw [Module.Basis.map_equivFun]
  simp

/-- The complete first-order equations follow for every chart from the
intrinsic equation and the actual local connection matrix. -/
theorem geodesic_coordinate_equation (C : Connection (tangentBundle S))
    {I : Set ℝ} {q : ℝ → Phase S} (hq : IsGeodesicOn S C I q)
    {t : ℝ} (ht : t ∈ I)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (hp : (q t).1 ∈ (tangentBundle S).baseSet c) :
    HasDerivAt (fun s => (c.val (q s).1).val) (chartVelocity S c q t) t ∧
    HasDerivAt (chartVelocity S c q)
      (coordinateAcceleration S C c ⟨(q t).1, hp⟩ (chartVelocity S c q t)) t := by
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hcoeff : chartVelocity S c q t = (b.basis ⟨(q t).1, hp⟩).equivFun (q t).2 :=
    CurveCovariantDerivative.coefficientsAlong_of_mem b
      (fun s => (q s).1) (fun s => (q s).2) t hp
  have hp' : (q t).1 ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
  constructor
  · have hd := CurveCovariantDerivative.velocity_coordinates (hq t ht).1
      (mem_univ t) c.val c.property hp'
    rw [hasDerivWithinAt_univ] at hd
    rw [hcoeff, trivializationFrame_equivFun]
    change HasDerivAt (fun s => (c.val (q s).1).val)
      (((tangentBundle S).trivialization c) ⟨(q t).1, (q t).2⟩).2 t
    rw [(tangentRealization S).coordinates c (q t).1 hp' (q t).2]
    exact hd
  · have hd := geodesic_frame_equation C hq ht b hp
    change HasDerivAt (chartVelocity S c q)
      (- (connectionMatrix C b ⟨(q t).1, hp⟩ (q t).2).mulVec
        (chartVelocity S c q t)) t at hd
    rw [hcoeff] at hd
    rw [hcoeff, coordinateAcceleration_eq_matrix]
    exact hd

/-- The local first-order coordinate equations also imply the intrinsic
geodesic equation at a point; continuity is needed only for the base curve.
This is a pointwise equivalence and assumes neither smoothness nor existence
of a spray. -/
theorem coordinate_equation_implies_geodesic_at
    (C : Connection (tangentBundle S)) (q : ℝ → Phase S) (t : ℝ)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (hp : (q t).1 ∈ (tangentBundle S).baseSet c)
    (hc : ContinuousAt (fun s => (q s).1) t)
    (hx : HasDerivAt (fun s => (c.val (q s).1).val) (chartVelocity S c q t) t)
    (hv : HasDerivAt (chartVelocity S c q)
      (coordinateAcceleration S C c ⟨(q t).1, hp⟩ (chartVelocity S c q t)) t) :
    HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2 ∧
      HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => (q s).2) t 0 := by
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hcoeff : chartVelocity S c q t = (b.basis ⟨(q t).1, hp⟩).equivFun (q t).2 :=
    CurveCovariantDerivative.coefficientsAlong_of_mem b
      (fun s => (q s).1) (fun s => (q s).2) t hp
  have hp' : (q t).1 ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
  have hvelocity : HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2 := by
    refine ⟨hc.continuousWithinAt, c.val, c.property, hp', ?_⟩
    rw [hcoeff, trivializationFrame_equivFun] at hx
    change HasDerivAt (fun s => (c.val (q s).1).val)
      (((tangentBundle S).trivialization c) ⟨(q t).1, (q t).2⟩).2 t at hx
    rw [(tangentRealization S).coordinates c (q t).1 hp' (q t).2] at hx
    exact hx.hasDerivWithinAt
  refine ⟨hvelocity, (covariant_acceleration_eq_zero_iff C hvelocity b hp hv).mpr ?_⟩
  change coordinateAcceleration S C c ⟨(q t).1, hp⟩ (chartVelocity S c q t) +
    (connectionMatrix C b ⟨(q t).1, hp⟩ (q t).2).mulVec (chartVelocity S c q t) = 0
  rw [hcoeff, coordinateAcceleration_eq_matrix]
  exact neg_add_cancel _

/-- Coordinate prescriptions determine a spray uniquely in the original
intrinsic tangent fibers, even in dimension zero. -/
theorem spray_unique (C : Connection (tangentBundle S))
    (G H : SmoothManifolds.VectorFieldData.SmoothField (tangentStructure (phaseManifold S)))
    (hG : HasSprayCoordinates S C G) (hH : HasSprayCoordinates S C H) : G = H := by
  have hval : G.val = H.val := by
    funext z
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 z.1
    let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc⟩
    have hp' : z.1 ∈ (tangentBundle S).baseSet i := by
      rw [(tangentRealization S).baseSet i]
      exact hp
    have heq := (hG i ⟨z.1, hp'⟩ z.2).trans (hH i ⟨z.1, hp'⟩ z.2).symm
    exact LinearEquiv.injective _ heq
  cases G
  cases H
  cases hval
  rfl

theorem pairing_sum (g : RiemannianMetric S) (p : M)
    (d z : Fin n → TangentSpace S p) :
    pairing g p (∑ i, d i) (∑ j, z j) =
      ∑ i, ∑ j, pairing g p (d i) (z j) := by
  rw [LinearMap.map_sum₂]
  apply Finset.sum_congr rfl
  intro i _
  exact map_sum (pairing g p (d i)) z Finset.univ

/-- Metric compatibility extends from smooth ambient fields to actual
parameter-differentiable fields along a curve. The finite representation used
here is the proved upstream representation, not a smooth extension of f. -/
theorem pairing_self_derivative
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    {V D : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    (hD : HasCovariantDerivativeAt C c f t D) :
    HasDerivAt (fun s => pairing g (c s) (f s) (f s))
      (pairing g (c t) D (f t) + pairing g (c t) (f t) D) t := by
  classical
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have hVX : HasVelocityWithinAt S c univ t (X.val (c t)) := hX ▸ hV
  obtain ⟨a, a', e, ha, hf, hDexp⟩ :=
    InducedConnections.curve_derivative_representation C X (mem_univ t)
      uniqueDiffWithinAt_univ hVX hD
  simp only [hasDerivWithinAt_univ] at ha
  rw [nhdsWithin_univ] at hf
  have hfval : f t = ∑ i, a i t • (e i).val (c t) :=
    Filter.Eventually.self_of_nhds (x := t)
      (p := fun s : ℝ => f s = ∑ i, a i s • (e i).val (c s)) hf
  let B (i j : Fin n) (s : ℝ) := pairing g (c s) ((e i).val (c s)) ((e j).val (c s))
  let d (i : Fin n) := a' i • (e i).val (c t) + a i t • (C.cov X (e i)).val (c t)
  let z (i : Fin n) := a i t • (e i).val (c t)
  have hB (i j : Fin n) : HasDerivAt (B i j)
      (pairing g (c t) ((C.cov X (e i)).val (c t)) ((e j).val (c t)) +
       pairing g (c t) ((e i).val (c t)) ((C.cov X (e j)).val (c t))) t := by
    have hs := SmoothMetrics.metric_pairing_smoothAt S (tangentBundle S) g id
      (e i).val (e j).val (c t)
      ((SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val
        S.smoothStructure.property.1) (c t)) ((e i).property (c t)) ((e j).property (c t))
    have hd := CurveCovariantDerivative.scalar_chain hVX
      (fun p => pairing g p ((e i).val p) ((e j).val p)) hs
    rw [hasDerivWithinAt_univ, hC X (e i) (e j) (c t)] at hd
    exact hd
  let H (i j : Fin n) :=
    a' i * (a j t * B i j t) + a i t *
      (a' j * B i j t + a j t *
        (pairing g (c t) ((C.cov X (e i)).val (c t)) ((e j).val (c t)) +
         pairing g (c t) ((e i).val (c t)) ((C.cov X (e j)).val (c t))))
  have hd : HasDerivAt (fun s => ∑ i : Fin n, ∑ j : Fin n,
      a i s * (a j s * B i j s)) (∑ i : Fin n, ∑ j : Fin n, H i j) t := by
    have hraw := HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      HasDerivAt.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        (ha i).mul ((ha j).mul (hB i j))))
    have hfun : (∑ i : Fin n, ∑ j : Fin n, a i * (a j * B i j)) =
        (fun s => ∑ i : Fin n, ∑ j : Fin n, a i s * (a j s * B i j s)) := by
      funext s
      simp only [Finset.sum_apply, Pi.mul_apply]
    rw [hfun] at hraw
    exact hraw
  have hH (i j : Fin n) : H i j =
      pairing g (c t) (d i) (z j) + pairing g (c t) (z i) (d j) := by
    dsimp only [H, B, d, z]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hsum : (∑ i : Fin n, ∑ j : Fin n, H i j) =
      pairing g (c t) D (f t) + pairing g (c t) (f t) D := by
    rw [hfval, hDexp]
    change (∑ i, ∑ j, H i j) =
      pairing g (c t) (∑ i, d i) (∑ j, z j) +
      pairing g (c t) (∑ i, z i) (∑ j, d j)
    rw [pairing_sum, pairing_sum]
    simp only [hH, Finset.sum_add_distrib]
  rw [hsum] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hf] with s hs
  rw [hs, pairing_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  dsimp only [B]
  ring

theorem speed_is_constant
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) {s t : ℝ} (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    tangentNorm g (q s).1 (q s).2 = tangentNorm g (q t).1 (q t).2 := by
  let f (t : ℝ) := pairing g (q t).1 (q t).2 (q t).2
  have hd (t : ℝ) (ht : t ∈ I.carrier) : HasDerivAt f 0 t := by
    have h := pairing_self_derivative g C hC.2 (hq t ht).1 (hq t ht).2
    simpa only [map_zero, LinearMap.zero_apply, add_zero] using h
  have heq : f s = f t := I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hs ht
  exact congrArg Real.sqrt heq

/-- Smoothness of the actual tangent lift implies joint smoothness of its
position, by the proved smooth tangent projection. -/
theorem positionSmoothAt_of_flowSmoothAt
    (F : SmoothManifolds.MaximalFlowData.CurveFamily (Phase S))
    (z : ℝ × Phase S)
    (hF : SmoothManifolds.MaximalFlowData.FlowSmoothAt (phaseManifold S) F z) :
    PositionSmoothAt S F z := by
  let π : Phase S → M := Sigma.fst
  have hπ := SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S)
  refine ⟨ContinuousAt.comp (f := SmoothManifolds.MaximalFlowData.flow F)
    (hπ (F.curve z.2 z.1)).1 hF.1, ?_⟩
  intro e he d hd hz hdz
  obtain ⟨c, hc, hqc⟩ := (phaseManifold S).smoothStructure.property.1.1 (F.curve z.2 z.1)
  obtain ⟨W, hW, hqW, K, hK, heqK⟩ := (hπ (F.curve z.2 z.1)).2 c hc d hd hqc hdz
  obtain ⟨V, hV, hzV, H, hH, heqH⟩ := hF.2 e he c hc hz hqc
  let U := V ∩ H ⁻¹' W
  have hU : IsOpen U := hH.continuousOn.isOpen_inter_preimage hV hW
  have hzU : (z.1, (e z.2).val) ∈ U := by
    refine ⟨hzV, ?_⟩
    change H (z.1, (e z.2).val) ∈ W
    rw [heqH.eq_of_nhds]
    exact hqW
  refine ⟨U, hU, hzU, K ∘ H, hK.comp (hH.mono inter_subset_left) (fun _ h => h.2), ?_⟩
  have heqK' := heqK.comp_tendsto hF.1
  filter_upwards [heqH, heqK'] with w hHw hKw
  exact (congrArg K hHw).trans hKw

/-- The inverse image of an open interval by a nonconstant affine map,
including negative scale and infinite endpoints. -/
def affineInterval (I : D13Unified.OpenTimeInterval) (a b : ℝ) (ha : a ≠ 0) :
    D13Unified.OpenTimeInterval where
  carrier := affineDomain I.carrier a b
  nonempty := by
    obtain ⟨t, ht⟩ := I.nonempty
    refine ⟨a⁻¹ * (t - b), ?_⟩
    change a * (a⁻¹ * (t - b)) + b ∈ I.carrier
    simpa only [← mul_assoc, mul_inv_cancel₀ ha, one_mul, sub_add_cancel] using ht
  ordConnected := by
    rcases lt_or_gt_of_ne ha with ha | ha
    · exact I.ordConnected.preimage_anti (fun _ _ h =>
        by simpa only [add_comm] using
          (add_le_add_right (mul_le_mul_of_nonpos_left h ha.le) b))
    · exact I.ordConnected.preimage_mono (fun _ _ h =>
        by simpa only [add_comm] using
          (add_le_add_right (mul_le_mul_of_nonneg_left h ha.le) b))
  isOpen := I.isOpen.preimage ((continuous_const.mul continuous_id).add continuous_const)

/-- Algebraic composition of affine changes on the actual tangent fibers. -/
theorem affineCurve_comp (q : ℝ → Phase S) (a b c d : ℝ) :
    affineCurve S (affineCurve S q a b) c d =
      affineCurve S q (a * c) (a * d + b) := by
  funext t
  have ht : a * (c * t + d) + b = (a * c) * t + (a * d + b) := by ring
  have hscale (z : Phase S) : (⟨z.1, c • (a • z.2)⟩ : Phase S) =
      ⟨z.1, (a * c) • z.2⟩ := by
    congr 1
    rw [smul_smul, mul_comm c a]
  exact (hscale (q (a * (c * t + d) + b))).trans
    (congrArg (fun s => (⟨(q s).1, (a * c) • (q s).2⟩ : Phase S)) ht)

open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.VectorFieldData SmoothManifolds.IntegralCurveData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.GeodesicData
open Set Filter
open scoped Topology

/-- Recover continuity from a single chart and eventual source containment. -/
theorem continuousAt_of_chart {n : ℕ} {M : Type u} [TopologicalSpace M]
    {q : ℝ → M} {t : ℝ} (e : ModelChart n .euclidean M)
    (hsource : ∀ᶠ s in 𝓝 t, q s ∈ e.source)
    (hc : ContinuousAt (fun s => (e (q s)).val) t) : ContinuousAt q t := by
  have hmodel : ContinuousAt (fun s => e (q s)) t := tendsto_subtype_rng.mpr hc
  have hlift := (e.continuousAt_symm (e.map_source hsource.self_of_nhds)).comp
    (f := fun s => e (q s)) hmodel
  exact hlift.congr (hsource.mono (fun s hs => e.left_inv hs))

/-- In a fixed chart, the intrinsic first-order equation bootstraps to smoothness. -/
theorem smoothAt_of_chart_equation {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) {I : Set ℝ} (hI : IsOpen I) {q : ℝ → M}
    (hc : ContinuousOn q I)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hd : ∀ s ∈ I, ∀ hs : q s ∈ e.source,
      HasDerivAt (fun r => (e (q r)).val)
        (B.fiberCoordinates.equiv e he (q s) hs (X.val (q s))) s)
    {t : ℝ} (ht : t ∈ I) (hp : q t ∈ e.source) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun r => (e (q r)).val) t := by
  obtain ⟨U, F, hU, hpU, hF, hrep⟩ :=
    SmoothManifolds.IntegralCurves.coefficient_extension X e he (q t) hp
  let J := I ∩ q ⁻¹' e.source ∩ (fun s => (e (q s)).val) ⁻¹' U
  have hJ0 : IsOpen (I ∩ q ⁻¹' e.source) :=
    hc.isOpen_inter_preimage hI e.open_source
  have hcoord : ContinuousOn (fun s => (e (q s)).val) (I ∩ q ⁻¹' e.source) :=
    continuous_subtype_val.continuousOn.comp
      (e.continuousOn.comp (hc.mono inter_subset_left) (fun s hs => hs.2))
      (fun _ _ => mem_univ _)
  have hJ : IsOpen J := hcoord.isOpen_inter_preimage hJ0 hU
  have htJ : t ∈ J := ⟨⟨ht, hp⟩, hpU⟩
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (fun s => (e (q s)).val) J := by
    apply SmoothManifolds.IntegralCurves.smooth_of_autonomous hJ hF
      (hcoord.mono inter_subset_left) (fun s hs => hs.2)
    intro s hs
    have hFp := (hrep (e (q s)).val hs.2).2
    simp only [SmoothManifolds.IntegralCurves.modelPoint] at hFp
    rw [e.left_inv hs.1.2] at hFp
    rw [SmoothManifolds.TangentBundle.chartFiber_eq S B e he ⟨q s, X.val (q s)⟩ hs.1.2] at hFp
    rw [hFp]
    exact hd s hs.1.1 hs.1.2
  exact hcd.contDiffAt (hJ.mem_nhds htJ)

/-- A continuous curve satisfying the intrinsic derivative equation in one
chart at each time is an integral curve, including the smoothness clause. -/
theorem integral_of_chart_derivatives {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) {I : Set ℝ} (hI : IsOpen I) {q : ℝ → M}
    (hc : ContinuousOn q I)
    (hd : ∀ t ∈ I, ∃ (e : ModelChart n .euclidean M)
      (he : e ∈ S.smoothStructure.val) (ht : q t ∈ e.source),
      HasDerivAt (fun s => (e (q s)).val)
        (B.fiberCoordinates.equiv e he (q t) ht (X.val (q t))) t) :
    IsIntegralCurveOn X I q := by
  have hall : ∀ t ∈ I, ∀ (d : ModelChart n .euclidean M)
      (hdm : d ∈ S.smoothStructure.val) (hdt : q t ∈ d.source),
      HasDerivAt (fun s => (d (q s)).val)
        (B.fiberCoordinates.equiv d hdm (q t) hdt (X.val (q t))) t := by
    intro t ht d hdm hdt
    obtain ⟨e, he, hp, hd⟩ := hd t ht
    obtain ⟨U, hU, hpU, F, hF, hrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 e he d hdm) hp hdt
    have heq := hrep.comp_tendsto (hc.continuousAt (hI.mem_nhds ht))
    have hdF := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t hd
    have hvel := SmoothManifolds.TangentBundle.transition_jacobian S B.fiberCoordinates
      e d he hdm (q t) hp hdt U F hU hpU hF hrep (X.val (q t))
    exact hvel ▸ hdF.congr_of_eventuallyEq heq.symm
  refine ⟨hc, ?_⟩
  intro t ht d hdm hdt
  exact ⟨smoothAt_of_chart_equation X hI hc d hdm
    (fun s hs hp => hall s hs d hdm hp) ht hdt, hall t ht d hdm hdt⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Tangent frame coordinates coincide with the original intrinsic coordinates. -/
theorem chartVelocity_eq
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (q : ℝ → Phase S) (t : ℝ)
    (hp : (q t).1 ∈ c.val.source) :
    chartVelocity S c q t = (tangentStructure S).fiberCoordinates.equiv
      c.val c.property (q t).1 hp (q t).2 := by
  have hb : (q t).1 ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hp
  rw [chartVelocity, P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ t hb]
  change (((Pi.basisFun ℝ (Fin n)).map
    ((tangentBundle S).fiberCoordinates c (q t).1 hb).symm).equivFun (q t).2) = _
  rw [Module.Basis.map_equivFun]
  simp only [Pi.basisFun_equivFun, LinearEquiv.symm_symm]
  change (((tangentBundle S).trivialization c) ⟨(q t).1, (q t).2⟩).2 = _
  exact (tangentRealization S).coordinates c (q t).1 hp (q t).2

/-- An actual phase chart is locally the packed position and velocity. -/
theorem phase_chart_eventuallyEq
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (q : ℝ → Phase S) (t : ℝ)
    (hp : (q t).1 ∈ c.val.source)
    (hc : ContinuousAt (fun s => (q s).1) t) :
    (fun s => (((tangentStructure S).chart c.val c.property) (q s)).val) =ᶠ[𝓝 t]
      (fun s => (tangentStructure S).productCoordinates.linearEquiv
        ((c.val (q s).1).val, chartVelocity S c q s)) := by
  have hev := hc.preimage_mem_nhds (c.val.open_source.mem_nhds hp)
  filter_upwards [hev] with s hs
  rw [(tangentStructure S).chart_apply c.val c.property (q s) hs,
    chartVelocity_eq c q s hs]


/-- Position and fiber coordinate derivatives give the actual phase derivative. -/
theorem phase_chart_hasDerivAt
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (q : ℝ → Phase S) (t : ℝ)
    (hp : (q t).1 ∈ c.val.source)
    (hc : ContinuousAt (fun s => (q s).1) t)
    {w a : Euclidean n}
    (hx : HasDerivAt (fun s => (c.val (q s).1).val) w t)
    (hv : HasDerivAt (chartVelocity S c q) a t) :
    HasDerivAt (fun s => (((tangentStructure S).chart c.val c.property) (q s)).val)
      ((tangentStructure S).productCoordinates.linearEquiv (w, a)) t := by
  have h := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    t (hx.prodMk hv)
  exact h.congr_of_eventuallyEq (phase_chart_eventuallyEq c q t hp hc)

/-- Recover continuity of the original phase curve from these two derivatives. -/
theorem phase_continuousAt
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (q : ℝ → Phase S) (t : ℝ)
    (hp : (q t).1 ∈ c.val.source)
    (hc : ContinuousAt (fun s => (q s).1) t)
    {w a : Euclidean n}
    (hx : HasDerivAt (fun s => (c.val (q s).1).val) w t)
    (hv : HasDerivAt (chartVelocity S c q) a t) :
    ContinuousAt q t := by
  apply continuousAt_of_chart ((tangentStructure S).chart c.val c.property)
  · filter_upwards [hc.preimage_mem_nhds (c.val.open_source.mem_nhds hp)] with s hs
    change q s ∈ ((tangentStructure S).chart c.val c.property).source
    rw [(tangentStructure S).chart_source]
    exact hs
  · exact (phase_chart_hasDerivAt c q t hp hc hx hv).continuousAt

/-- The phase derivative decomposes into the actual two local equations. -/
theorem phase_chart_hasDerivAt_iff
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (q : ℝ → Phase S) (t : ℝ)
    (hp : (q t).1 ∈ c.val.source)
    (hc : ContinuousAt (fun s => (q s).1) t)
    {w a : Euclidean n} :
    HasDerivAt (fun s => (((tangentStructure S).chart c.val c.property) (q s)).val)
      ((tangentStructure S).productCoordinates.linearEquiv (w, a)) t ↔
    HasDerivAt (fun s => (c.val (q s).1).val) w t ∧
      HasDerivAt (chartVelocity S c q) a t := by
  constructor
  · intro hd
    have h := (tangentStructure S).productCoordinates.linearEquiv.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
    have heq :
        (fun s => (tangentStructure S).productCoordinates.linearEquiv.symm
          ((((tangentStructure S).chart c.val c.property) (q s)).val)) =ᶠ[𝓝 t]
        (fun s => ((c.val (q s).1).val, chartVelocity S c q s)) := by
      filter_upwards [phase_chart_eventuallyEq c q t hp hc] with s hs
      simp only [hs, ContinuousLinearEquiv.symm_apply_apply]
    have h' := h.congr_of_eventuallyEq heq.symm
    change HasDerivAt _ ((tangentStructure S).productCoordinates.linearEquiv.symm
      ((tangentStructure S).productCoordinates.linearEquiv (w, a))) t at h'
    rw [ContinuousLinearEquiv.symm_apply_apply] at h' 
    exact ⟨h'.fst, h'.snd⟩
  · rintro ⟨hx, hv⟩
    exact phase_chart_hasDerivAt c q t hp hc hx hv
/-- The spray equations are equivalent to the original geodesic equations. -/
theorem integralCurve_iff_geodesic
    (C : Connection (tangentBundle S))
    (G : SmoothField (tangentStructure (phaseManifold S)))
    (hG : HasSprayCoordinates S C G)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) :
    IsIntegralCurveOn G I.carrier q ↔ IsGeodesicOn S C I.carrier q := by
  have coordinates (t : ℝ)
      (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
      (hpB : (q t).1 ∈ (tangentBundle S).baseSet c)
      (hp : (q t).1 ∈ c.val.source) :
      let e := (tangentStructure S).chart c.val c.property
      let he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S)
        c.val c.property
      let hz : q t ∈ e.source := by
        rw [(tangentStructure S).chart_source]
        exact hp
      (tangentStructure (phaseManifold S)).fiberCoordinates.equiv e he (q t) hz
        (G.val (q t)) =
      (tangentStructure S).productCoordinates.linearEquiv
        (chartVelocity S c q t,
          coordinateAcceleration S C c ⟨(q t).1, hpB⟩ (chartVelocity S c q t)) := by
    have h := hG c ⟨(q t).1, hpB⟩ (q t).2
    dsimp only at h
    rw [← chartVelocity_eq c q t hp] at h
    exact h
  constructor
  · intro hq t ht
    obtain ⟨d, hd, hp⟩ := S.smoothStructure.property.1.1 (q t).1
    let c : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨d, hd⟩
    have hpB : (q t).1 ∈ (tangentBundle S).baseSet c := by
      rw [(tangentRealization S).baseSet c]
      exact hp
    have hc : ContinuousAt (fun s => (q s).1) t :=
      ((SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S)
        (q t)).1).comp (hq.1.continuousAt (I.isOpen.mem_nhds ht))
    let e := (tangentStructure S).chart c.val c.property
    have he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S)
      c.val c.property
    have hz : q t ∈ e.source := by
      rw [(tangentStructure S).chart_source]
      exact hp
    have hder := (hq.2 t ht e he hz).2
    rw [coordinates t c hpB hp] at hder
    have heqs := (phase_chart_hasDerivAt_iff c q t hp hc).mp hder
    exact P202.Geometry.GeodesicIVP.coordinate_equation_implies_geodesic_at
      C q t c hpB hc heqs.1 heqs.2
  · intro hq
    have hdata (t : ℝ) (ht : t ∈ I.carrier) :
        ∃ (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
          (hp : (q t).1 ∈ c.val.source),
          ContinuousAt (fun s => (q s).1) t ∧
          HasDerivAt
            (fun s => (((tangentStructure S).chart c.val c.property) (q s)).val)
            ((tangentStructure S).productCoordinates.linearEquiv
              (chartVelocity S c q t,
                coordinateAcceleration S C c
                  ⟨(q t).1, ((tangentRealization S).baseSet c).symm ▸ hp⟩
                  (chartVelocity S c q t))) t := by
      obtain ⟨d, hd, hp⟩ := S.smoothStructure.property.1.1 (q t).1
      let c : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨d, hd⟩
      have hpB : (q t).1 ∈ (tangentBundle S).baseSet c := by
        rw [(tangentRealization S).baseSet c]
        exact hp
      have hc : ContinuousAt (fun s => (q s).1) t := by
        simpa only [continuousWithinAt_univ] using (hq t ht).1.1
      obtain ⟨hx, hv⟩ :=
        P202.Geometry.GeodesicIVP.geodesic_coordinate_equation C hq ht c hpB
      exact ⟨c, hp, hc, phase_chart_hasDerivAt c q t hp hc hx hv⟩
    have hc : ContinuousOn q I.carrier := by
      intro t ht
      obtain ⟨c, hp, hc, hd⟩ := hdata t ht
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_of_chart ((tangentStructure S).chart c.val c.property)
      · filter_upwards [hc.preimage_mem_nhds (c.val.open_source.mem_nhds hp)] with s hs
        rw [(tangentStructure S).chart_source]
        exact hs
      · exact hd.continuousAt
    apply integral_of_chart_derivatives G I.isOpen hc
    intro t ht
    obtain ⟨c, hp, hc, hd⟩ := hdata t ht
    have hpB : (q t).1 ∈ (tangentBundle S).baseSet c := by
      rw [(tangentRealization S).baseSet c]
      exact hp
    let e := (tangentStructure S).chart c.val c.property
    have he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S)
      c.val c.property
    have hz : q t ∈ e.source := by
      rw [(tangentStructure S).chart_source]
      exact hp
    refine ⟨e, he, hz, ?_⟩
    rw [coordinates t c hpB hp]
    exact hd


open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.VectorFieldData SmoothManifolds.MapData
  P202.ConnectionData P202.MetricData P202.GeodesicData P202.LeviCivitaData
open Set
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A coordinate test for a raw intrinsic section of T(TM). The test uses just
one of the actual tangent charts over each point, selected from the base atlas.
The functions W are total representatives, smooth only on the relevant source. -/
theorem section_smooth_of_tangentChart_coordinates
    (X : SmoothManifolds.VectorFieldData.Section (phaseManifold S))
    (W : SmoothManifolds.BundleOperationsData.TangentIndex S →
      Phase S → Euclidean (n + n))
    (hW : ∀ c z, z.1 ∈ c.val.source →
      SmoothManifolds.FrameData.VectorSmoothAt (phaseManifold S).smoothStructure.val (W c) z)
    (hX : ∀ (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
      (z : Phase S) (hz : z.1 ∈ c.val.source),
      let e := (tangentStructure S).chart c.val c.property
      let he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) c.val c.property
      let hz' : z ∈ e.source := by
        simpa only [e, TangentBundleStructure.chart_source, projection, mem_preimage] using hz
      (tangentStructure (phaseManifold S)).fiberCoordinates.equiv e he z hz' (X z) = W c z) :
    letI := (tangentStructure (phaseManifold S)).topology
    IsSmoothMap (phaseManifold S) (tangentStructure (phaseManifold S)).manifold
      (fun z => ⟨z, X z⟩) := by
  intro z
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 z.1
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc⟩
  let e := (tangentStructure S).chart c hc
  have he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) c hc
  have hz : z ∈ e.source := by
    simpa only [e, TangentBundleStructure.chart_source, projection, mem_preimage] using hp
  apply SmoothManifolds.VectorFields.section_smoothAt_of_coordinates
    (phaseManifold S) (tangentStructure (phaseManifold S)) X z e he hz
    e.source e.open_source hz (fun _ h => h) (W i) (hW i z hp)
  intro y hy
  have hyp : y.1 ∈ c.source := by
    simpa only [e, TangentBundleStructure.chart_source, projection, mem_preimage] using hy
  exact (hX i y hyp).symm

/-- The local spray formula as a total representative on phase space. Its
values outside the tangent chart source are immaterial. -/
noncomputable def sprayCoordinateFunction (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (z : Phase S) :
    Euclidean (n + n) := by
  classical
  exact if hp : z.1 ∈ (tangentBundle S).baseSet c then
    let hs : z.1 ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
    let w := (tangentStructure S).fiberCoordinates.equiv c.val c.property z.1 hs z.2
    (tangentStructure S).productCoordinates.linearEquiv
      (w, coordinateAcceleration S C c ⟨z.1, hp⟩ w)
  else 0

/-- Expanded spray-coordinate prescription for a raw intrinsic section.
Smoothness is a separate conclusion, not part of this predicate. -/
def SectionHasSprayCoordinates (C : Connection (tangentBundle S))
    (X : SmoothManifolds.VectorFieldData.Section (phaseManifold S)) : Prop :=
  ∀ (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val),
    let hp : p.val ∈ c.val.source := (tangentRealization S).baseSet c ▸ p.property
    let z : Phase S := ⟨p.val, v⟩
    let e := (tangentStructure S).chart c.val c.property
    let he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) c.val c.property
    let hz : z ∈ e.source := by
      simpa only [e, TangentBundleStructure.chart_source, projection, mem_preimage] using hp
    let w := (tangentStructure S).fiberCoordinates.equiv c.val c.property p.val hp v
    (tangentStructure (phaseManifold S)).fiberCoordinates.equiv e he z hz (X z) =
      (tangentStructure S).productCoordinates.linearEquiv
        (w, coordinateAcceleration S C c p w)

/-- Smooth local right hand sides turn a chart-compatible intrinsic spray
section into an actual smooth field on the original tangent bundle. -/
theorem spray_section_smooth (C : Connection (tangentBundle S))
    (X : SmoothManifolds.VectorFieldData.Section (phaseManifold S))
    (hX : SectionHasSprayCoordinates C X)
    (hW : ∀ c z, z.1 ∈ c.val.source →
      SmoothManifolds.FrameData.VectorSmoothAt (phaseManifold S).smoothStructure.val
        (sprayCoordinateFunction C c) z) :
    letI := (tangentStructure (phaseManifold S)).topology
    IsSmoothMap (phaseManifold S) (tangentStructure (phaseManifold S)).manifold
      (fun z => ⟨z, X z⟩) := by
  apply section_smooth_of_tangentChart_coordinates X (sprayCoordinateFunction C) hW
  intro c z hz
  have hp : z.1 ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hz
  simpa only [sprayCoordinateFunction, dite_eq_left hp] using hX c ⟨z.1, hp⟩ z.2

/-- Construct the smooth field once the raw intrinsic section has been glued.
Its intrinsic values are definitionally the supplied section. -/
noncomputable def sprayFieldOfCoordinates (C : Connection (tangentBundle S))
    (X : SmoothManifolds.VectorFieldData.Section (phaseManifold S))
    (hX : SectionHasSprayCoordinates C X)
    (hW : ∀ c z, z.1 ∈ c.val.source →
      SmoothManifolds.FrameData.VectorSmoothAt (phaseManifold S).smoothStructure.val
        (sprayCoordinateFunction C c) z) :
    SmoothField (tangentStructure (phaseManifold S)) :=
  ⟨X, spray_section_smooth C X hX hW⟩

theorem sprayFieldOfCoordinates_coordinates (C : Connection (tangentBundle S))
    (X : SmoothManifolds.VectorFieldData.Section (phaseManifold S))
    (hX : SectionHasSprayCoordinates C X)
    (hW : ∀ c z, z.1 ∈ c.val.source →
      SmoothManifolds.FrameData.VectorSmoothAt (phaseManifold S).smoothStructure.val
        (sprayCoordinateFunction C c) z) :
    HasSprayCoordinates S C (sprayFieldOfCoordinates C X hX hW) := hX


open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.FrameData SmoothManifolds.MapData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.GeodesicData
open Set Filter
open scoped Topology
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem tangent_baseSet_isOpen
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) :
    IsOpen ((tangentBundle S).baseSet c) := by
  rw [(tangentRealization S).baseSet c]
  exact c.val.open_source

theorem christoffel_smooth (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (k i j : Fin n) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val
      ((tangentBundle S).baseSet c) (tangent_baseSet_isOpen c))
      (fun p => P202.LeviCivitaData.christoffel C c p k i j) := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  let X : LocalSection B (B.baseSet c) (tangent_baseSet_isOpen c) := ⟨b.section_ i, b.smooth i⟩
  let Y : LocalSection B (B.baseSet c) (tangent_baseSet_isOpen c) := ⟨b.section_ j, b.smooth j⟩
  have hs := ConnectionForms.covOn_smooth B C _ (tangent_baseSet_isOpen c) X Y
  have hc := (SmoothManifolds.Frames.smooth_section_iff_coefficients B _
    (tangent_baseSet_isOpen c) b (covOn C _ (tangent_baseSet_isOpen c) X Y)).mp hs k
  intro p
  apply (hc p).congr
  apply Eventually.of_forall
  intro q
  change (b.basis q).equivFun (covOn C _ _ X Y q) k = _
  rw [← ConnectionForms.connectionForm_characterization B C b X q k j]
  change connectionForm C b q k j (b.section_ i q) =
    connectionForm C b q k j (P202.LeviCivitaData.coordinateVector c i q.val)
  rw [← b.basis_eq, coordinateVector_eq_frame]

/-- The spray polynomial is smooth in the actual tangent chart domain. The
Christoffel entries are pulled back by the genuine smooth tangent projection,
while the fiber coordinates come from the genuine tangent chart. -/
theorem sprayCoordinateFunction_smooth (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (z : Phase S) (hz : z.1 ∈ c.val.source) :
    VectorSmoothAt (phaseManifold S).smoothStructure.val
      (sprayCoordinateFunction C c) z := by
  classical
  let T := tangentStructure S
  let w : Phase S → Euclidean n :=
    SmoothManifolds.TangentBundle.chartFiber T c.val c.property
  have hp : z.1 ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hz
  have hw : VectorSmoothAt (phaseManifold S).smoothStructure.val w z := by
    exact SmoothManifolds.TangentBundle.chartFiber_smoothAt S T (phaseManifold S)
      id z c.val c.property hz
      ((SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞)
        (phaseManifold S).smoothStructure.val (phaseManifold S).smoothStructure.property.1) z)
  let gamma (k i j : Fin n) : Phase S → ℝ := fun y =>
    SmoothManifolds.FrameData.totalize
      (fun p => P202.LeviCivitaData.christoffel C c p k i j) y.1
  have hg (k i j : Fin n) : VectorSmoothAt (phaseManifold S).smoothStructure.val
      (gamma k i j) z := by
    have hbase := SmoothManifolds.FrameData.VectorSmoothAt.totalize
      (tangent_baseSet_isOpen c) (christoffel_smooth C c k i j ⟨z.1, hp⟩)
    exact SmoothManifolds.FrameData.VectorSmoothAt.comp
      S.smoothStructure.property.1.1 hbase
      (SmoothManifolds.TangentBundle.projection_smooth S T z)
  have hwi (i : Fin n) : VectorSmoothAt (phaseManifold S).smoothStructure.val
      (fun y => w y i) z :=
    hw.postcomp (ContinuousLinearMap.proj i).contDiff
  let a : Phase S → Euclidean n := fun y k =>
    -∑ i : Fin n, ∑ j : Fin n, gamma k i j y * w y i * w y j
  have ha : VectorSmoothAt (phaseManifold S).smoothStructure.val a z := by
    apply SmoothManifolds.FrameData.VectorSmoothAt.pi
    intro k
    have hs : VectorSmoothAt (phaseManifold S).smoothStructure.val
        (fun y => ∑ i : Fin n, ∑ j : Fin n, gamma k i j y * w y i * w y j) z := by
      apply SmoothManifolds.FrameData.VectorSmoothAt.sum
      intro i
      apply SmoothManifolds.FrameData.VectorSmoothAt.sum
      intro j
      exact (((hg k i j).prod (hwi i)).postcomp
        (contDiff_fst.mul contDiff_snd)).prod (hwi j) |>.postcomp
          (contDiff_fst.mul contDiff_snd)
    exact hs.postcomp contDiff_neg
  have hpoly := (hw.prod ha).postcomp T.productCoordinates.linearEquiv.contDiff
  apply hpoly.congr
  have hnear : ∀ᶠ y : Phase S in 𝓝 z, y.1 ∈ c.val.source :=
    (SmoothManifolds.TangentBundle.projection_smooth S T z).1.preimage_mem_nhds
      (c.val.open_source.mem_nhds hz)
  filter_upwards [hnear] with y hy
  have hyp : y.1 ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hy
  simp only [sprayCoordinateFunction, dite_eq_left hyp]
  have hwval : w y = T.fiberCoordinates.equiv c.val c.property y.1 hy y.2 :=
    SmoothManifolds.TangentBundle.chartFiber_eq S T c.val c.property y hy
  apply congrArg T.productCoordinates.linearEquiv
  apply Prod.ext
  · exact hwval
  · ext k
    simp only [a, P202.GeodesicData.coordinateAcceleration, gamma,
      SmoothManifolds.FrameData.totalize_of_mem _ _ hyp, hwval]
    rfl


noncomputable def chartLine (e : ModelChart n .euclidean M) (p : M)
    (w : Euclidean n) (t : ℝ) : M :=
  e.symm ⟨(e p).val + t • w, mem_univ _⟩

@[simp] theorem chartLine_zero (e : ModelChart n .euclidean M)
    (p : M) (hp : p ∈ e.source) (w : Euclidean n) : chartLine e p w 0 = p := by
  simpa [chartLine] using e.left_inv hp

theorem chartLine_continuousAt (e : ModelChart n .euclidean M)
    (p : M) (hp : p ∈ e.source) (w : Euclidean n) :
    ContinuousAt (chartLine e p w) 0 := by
  have he : ContinuousAt (fun t : ℝ => (⟨(e p).val + t • w, mem_univ _⟩ : modelSet n .euclidean)) 0 :=
    ((continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _).continuousAt
  have htarget : (⟨(e p).val + (0 : ℝ) • w, mem_univ _⟩ : modelSet n .euclidean) ∈ e.target := by
    simpa using e.map_source hp
  exact (e.symm.continuousAt htarget).comp he

theorem chartLine_chart_germ (e : ModelChart n .euclidean M)
    (p : M) (hp : p ∈ e.source) (w : Euclidean n) :
    (fun t => (e (chartLine e p w t)).val) =ᶠ[𝓝 0]
      (fun t => (e p).val + t • w) := by
  have he : ContinuousAt (fun t : ℝ => (⟨(e p).val + t • w, mem_univ _⟩ : modelSet n .euclidean)) 0 :=
    ((continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _).continuousAt
  have htarget : (⟨(e p).val + (0 : ℝ) • w, mem_univ _⟩ : modelSet n .euclidean) ∈ e.target := by
    simpa using e.map_source hp
  filter_upwards [he.preimage_mem_nhds (e.open_target.mem_nhds htarget)] with t ht
  exact congrArg Subtype.val (e.right_inv ht)

theorem chartLine_deriv (e : ModelChart n .euclidean M)
    (p : M) (hp : p ∈ e.source) (w : Euclidean n) :
    HasDerivAt (fun t => (e (chartLine e p w t)).val) w 0 := by
  have hd : HasDerivAt (fun t : ℝ => (e p).val + t • w) w 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (e p).val
  exact hd.congr_of_eventuallyEq (chartLine_chart_germ e p hp w)

theorem chartLine_velocity (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (w : Euclidean n) :
    HasVelocityWithinAt S (chartLine e p w) univ 0
      (((tangentStructure S).fiberCoordinates.equiv e he (chartLine e p w 0)
        (by simpa only [chartLine_zero e p hp w] using hp)).symm w) := by
  refine ⟨(chartLine_continuousAt e p hp w).continuousWithinAt, e, he, ?_, ?_⟩
  · simpa only [chartLine_zero e p hp w] using hp
  · rw [LinearEquiv.apply_symm_apply]
    exact (chartLine_deriv e p hp w).hasDerivWithinAt

noncomputable def localSpray (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val) :
    TangentSpace (phaseManifold S) (⟨p.val, v⟩ : Phase S) := by
  let hp : p.val ∈ c.val.source := (tangentRealization S).baseSet c ▸ p.property
  let e := (tangentStructure S).chart c.val c.property
  let he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) c.val c.property
  let hz : (⟨p.val, v⟩ : Phase S) ∈ e.source := by
    simpa only [e, SmoothManifolds.TangentBundleData.TangentBundleStructure.chart_source,
      SmoothManifolds.TangentBundleData.projection, mem_preimage] using hp
  let w := (tangentStructure S).fiberCoordinates.equiv c.val c.property p.val hp v
  exact ((tangentStructure (phaseManifold S)).fiberCoordinates.equiv e he _ hz).symm
    ((tangentStructure S).productCoordinates.linearEquiv
      (w, coordinateAcceleration S C c p w))

theorem localSpray_coordinates (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val) :
    let hp : p.val ∈ c.val.source := (tangentRealization S).baseSet c ▸ p.property
    let z : Phase S := ⟨p.val, v⟩
    let e := (tangentStructure S).chart c.val c.property
    let he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) c.val c.property
    let hz : z ∈ e.source := by
      simpa only [e, SmoothManifolds.TangentBundleData.TangentBundleStructure.chart_source,
        SmoothManifolds.TangentBundleData.projection, mem_preimage] using hp
    let w := (tangentStructure S).fiberCoordinates.equiv c.val c.property p.val hp v
    (tangentStructure (phaseManifold S)).fiberCoordinates.equiv e he z hz (localSpray C c p v) =
      (tangentStructure S).productCoordinates.linearEquiv
        (w, coordinateAcceleration S C c p w) := by
  exact LinearEquiv.apply_symm_apply _ _

/-- Every base chart gives the same vector in the actual second tangent fiber.
The proof uses an affine curve in the first phase chart, and the already proved
frame-independence of covariant differentiation at its central point. -/
theorem localSpray_overlap (C : Connection (tangentBundle S))
    (c d : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (hdp : p.val ∈ (tangentBundle S).baseSet d)
    (v : TangentSpace S p.val) :
    localSpray C c p v = localSpray C d ⟨p.val, hdp⟩ v := by
  let B := tangentStructure S
  let K := tangentStructure (phaseManifold S)
  let z : Phase S := ⟨p.val, v⟩
  have hp : p.val ∈ c.val.source := (tangentRealization S).baseSet c ▸ p.property
  have hdp' : p.val ∈ d.val.source := (tangentRealization S).baseSet d ▸ hdp
  let e := B.chart c.val c.property
  have he : e ∈ (phaseManifold S).smoothStructure.val :=
    SmoothManifolds.TangentBundle.chart_mem S B c.val c.property
  have hz : z ∈ e.source := by
    simpa only [e, B, TangentBundleStructure.chart_source, projection, mem_preimage] using hp
  let w := B.fiberCoordinates.equiv c.val c.property p.val hp v
  let a := coordinateAcceleration S C c p w
  let W := B.productCoordinates.linearEquiv (w,a)
  let q : ℝ → Phase S := chartLine e z W
  have hq0 : q 0 = z := chartLine_zero e z hz W
  have hq : ContinuousAt q 0 := chartLine_continuousAt e z hz W
  have hbase : ContinuousAt (fun t => (q t).1) 0 :=
    ((SmoothManifolds.TangentBundle.projection_smooth S B) (q 0)).1.comp hq
  have hpc : (q 0).1 ∈ c.val.source := by simpa only [hq0] using hp
  have hpd : (q 0).1 ∈ d.val.source := by simpa only [hq0] using hdp'
  have hcoord := (phase_chart_hasDerivAt_iff c q 0 hpc hbase).mp
    (chartLine_deriv e z hz W)
  have hw0 : chartVelocity S c q 0 = w := by
    rw [chartVelocity_eq c q 0 hpc]
    rw [← SmoothManifolds.TangentBundle.chartFiber_eq S B c.val c.property (q 0) hpc,
      hq0, SmoothManifolds.TangentBundle.chartFiber_eq S B c.val c.property z hp]
  have hg : IsGeodesicOn S C {0} q := by
    intro t ht
    have ht0 : t = 0 := ht
    subst t
    have hpcb : (q 0).1 ∈ (tangentBundle S).baseSet c := by
      rw [(tangentRealization S).baseSet c]
      exact hpc
    apply coordinate_equation_implies_geodesic_at C q 0 c hpcb hbase
    · simpa only [hw0] using hcoord.1
    · convert hcoord.2 using 1 <;> simp only [hw0, hq0] <;> rfl
  have hpdb : (q 0).1 ∈ (tangentBundle S).baseSet d := by
    rw [(tangentRealization S).baseSet d]
    exact hpd
  have hdcoord := geodesic_coordinate_equation C hg (by simp) d hpdb
  have hdphase := phase_chart_hasDerivAt d q 0 hpd hbase hdcoord.1 hdcoord.2
  have hvel := chartLine_velocity (S := phaseManifold S) e he z hz W
  let f := B.chart d.val d.property
  have hf : f ∈ (phaseManifold S).smoothStructure.val :=
    SmoothManifolds.TangentBundle.chart_mem S B d.val d.property
  have hqf : q 0 ∈ f.source := by
    simpa only [f, B, TangentBundleStructure.chart_source, projection, mem_preimage] using hpd
  have hdvel := P202.Geometry.CurveCovariantDerivative.velocity_coordinates
    hvel (mem_univ 0) f hf hqf
  rw [hasDerivWithinAt_univ] at hdvel
  have heq := hdvel.unique hdphase
  have hw' : chartVelocity S d q 0 =
      B.fiberCoordinates.equiv d.val d.property p.val hdp' v := by
    rw [chartVelocity_eq d q 0 hpd]
    rw [← SmoothManifolds.TangentBundle.chartFiber_eq S B d.val d.property (q 0) hpd,
      hq0, SmoothManifolds.TangentBundle.chartFiber_eq S B d.val d.property z hdp']
  apply (K.fiberCoordinates.equiv f hf z (by simpa only [hq0] using hqf)).injective
  rw [localSpray_coordinates C d ⟨p.val,hdp⟩ v]
  rw [hw'] at heq
  change (K.fiberCoordinates.equiv f hf (q 0) hqf)
    (((K.fiberCoordinates.equiv e he (q 0) _).symm) W) = _ at heq
  have hpdeq : (⟨(q 0).1, hpdb⟩ : (tangentBundle S).baseSet d) = ⟨p.val, hdp⟩ :=
    Subtype.ext (congrArg Sigma.fst hq0)
  rw [hpdeq] at heq
  have htrans (z' : Phase S) (hze : z' ∈ e.source) (hzf : z' ∈ f.source)
      (h : z' = z) :
      (K.fiberCoordinates.equiv f hf z' hzf) ((K.fiberCoordinates.equiv e he z' hze).symm W) =
      (K.fiberCoordinates.equiv f hf z (by simpa only [hq0] using hqf)) (localSpray C c p v) := by
    subst z'
    rfl
  rw [htrans (q 0) _ _ hq0] at heq
  exact heq

/-- The base atlas covers each point, including the empty and zero dimensional cases. -/
theorem tangentIndex_exists (p : M) :
    ∃ c : SmoothManifolds.BundleOperationsData.TangentIndex S,
      p ∈ (tangentBundle S).baseSet c := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  refine ⟨⟨e,he⟩, ?_⟩
  rw [(tangentRealization S).baseSet]
  exact hp

/-- Choose one intrinsic local value. Overlap compatibility removes the choice. -/
noncomputable def spraySection (C : Connection (tangentBundle S)) :
    SmoothManifolds.VectorFieldData.Section (phaseManifold S) := fun z =>
  localSpray C (Classical.choose (tangentIndex_exists z.1))
    ⟨z.1, Classical.choose_spec (tangentIndex_exists z.1)⟩ z.2

theorem spraySection_local (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val) :
    spraySection C ⟨p.val,v⟩ = localSpray C c p v := by
  exact localSpray_overlap C (Classical.choose (tangentIndex_exists p.val)) c
    ⟨p.val, Classical.choose_spec (tangentIndex_exists p.val)⟩ p.property v

theorem spraySection_coordinates (C : Connection (tangentBundle S)) :
    SectionHasSprayCoordinates C (spraySection C) := by
  intro c p v
  dsimp only
  rw [spraySection_local C c p v]
  exact localSpray_coordinates C c p v

theorem spray_section_exists (C : Connection (tangentBundle S)) :
    ∃ X : SmoothManifolds.VectorFieldData.Section (phaseManifold S),
      SectionHasSprayCoordinates C X :=
  ⟨spraySection C, spraySection_coordinates C⟩


section SprayBridge
open SmoothManifolds.VectorFieldData SmoothManifolds.MaximalFlowData
variable (C : Connection (tangentBundle S))
    (G : SmoothField (tangentStructure (phaseManifold S)))
    (hbridge : ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      SmoothManifolds.IntegralCurveData.IsIntegralCurveOn G I.carrier q ↔
        IsGeodesicOn S C I.carrier q)
include G hbridge

/-- Once the spray bridge is proved, the library's universal maximality
property transfers without any change of domains or off-domain assertions. -/
theorem maximal_iff_integral (w : Phase S) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) :
    IsMaximalThrough S C w I q ↔
      SmoothManifolds.IntegralCurveData.IsMaximalThrough G w I q := by
  constructor
  · rintro ⟨h0, hi, hq, hmax⟩
    refine ⟨h0, hi, (hbridge I q).mpr hq, ?_⟩
    intro J r hJ hr hsol
    exact hmax J r hJ hr ((hbridge J r).mp hsol)
  · rintro ⟨h0, hi, hq, hmax⟩
    refine ⟨h0, hi, (hbridge I q).mp hq, ?_⟩
    intro J r hJ hr hsol
    exact hmax J r hJ hr ((hbridge J r).mpr hsol)

/-- Reduction to the actual maximal integral curve theorem. The spray and
its bridge are explicit arguments here; their construction remains required. -/
theorem maximal_exists_from_spray (w : Phase S) :
    ∃ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsMaximalThrough S C w I q := by
  obtain ⟨I, q, hq⟩ := SmoothManifolds.IntegralCurves.maximal_exists
    (phaseManifold S) (tangentStructure (phaseManifold S)) G w
  exact ⟨I, q, (maximal_iff_integral C G hbridge w I q).mpr hq⟩

theorem overlap_unique_from_spray (I J : D13Unified.OpenTimeInterval)
    (q r : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    (hr : IsGeodesicOn S C J.carrier r)
    (s : ℝ) (hs : s ∈ I.carrier ∩ J.carrier) (hmeet : q s = r s) :
    EqOn q r (I.carrier ∩ J.carrier) :=
  SmoothManifolds.IntegralCurves.overlap_unique
    (phaseManifold S) (tangentStructure (phaseManifold S)) G I J q r
    ((hbridge I q).mpr hq) ((hbridge J r).mpr hr) s hs hmeet

theorem domain_open_flowSmooth_from_spray
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) :
    IsOpen (flowDomain F) ∧ ∀ z ∈ flowDomain F, FlowSmoothAt (phaseManifold S) F z := by
  apply SmoothManifolds.MaximalFlow.domain_open_smooth
    (phaseManifold S) (tangentStructure (phaseManifold S)) G F
  intro w
  exact (maximal_iff_integral C G hbridge w (F.interval w) (F.curve w)).mp (hF w)

theorem domain_open_smooth_from_spray
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) :
    IsOpen (flowDomain F) ∧ ∀ z ∈ flowDomain F,
      FlowSmoothAt (phaseManifold S) F z ∧ PositionSmoothAt S F z := by
  obtain ⟨hopen, hsmooth⟩ := domain_open_flowSmooth_from_spray C G hbridge F hF
  exact ⟨hopen, fun z hz => ⟨hsmooth z hz, positionSmoothAt_of_flowSmoothAt F z (hsmooth z hz)⟩⟩

/-- A maximal geodesic absorbs any geodesic meeting it, even when the
comparison interval does not contain its original time zero. -/
theorem maximal_contains_from_spray
    {w : Phase S} {I J : D13Unified.OpenTimeInterval} {q r : ℝ → Phase S}
    (hq : IsMaximalThrough S C w I q) (hr : IsGeodesicOn S C J.carrier r)
    {s : ℝ} (hs : s ∈ I.carrier ∩ J.carrier) (hmeet : q s = r s) :
    J.carrier ⊆ I.carrier ∧ EqOn q r J.carrier := by
  exact SmoothManifolds.MaximalFlow.maximalThrough_contains
    SmoothManifolds.IntegralCurves.overlap_unique
    ((maximal_iff_integral C G hbridge w I q).mp hq)
    ((hbridge J r).mpr hr) hs hmeet

/-- Affine changes preserve the universal maximality property on precisely
the inverse-image time interval. The inverse-scaled competitor meets the
original curve at time b, so translation never requires b to be zero. -/
theorem maximal_affine_from_spray
    {w : Phase S} {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (hq : IsMaximalThrough S C w I q) (a b : ℝ) (ha : a ≠ 0) (hb : b ∈ I.carrier) :
    ∃ J : D13Unified.OpenTimeInterval,
      J.carrier = affineDomain I.carrier a b ∧
      IsMaximalThrough S C (affineCurve S q a b 0) J (affineCurve S q a b) := by
  let J := affineInterval I a b ha
  refine ⟨J, rfl, ?_⟩
  refine ⟨by simpa [J, affineInterval, affineDomain] using hb, rfl,
    geodesic_affine C a b hq.2.2.1, ?_⟩
  intro K r h0 hr0 hr
  let L := affineInterval K a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha)
  let back := affineCurve S r a⁻¹ (-a⁻¹ * b)
  have hback : IsGeodesicOn S C L.carrier back := geodesic_affine C _ _ hr
  have hbL : b ∈ L.carrier := by
    change a⁻¹ * b + -a⁻¹ * b ∈ K.carrier
    simpa only [neg_mul, add_neg_cancel] using h0
  have hmeet : q b = back b := by
    have htime : a⁻¹ * b + -a⁻¹ * b = 0 := by ring
    have hr0' : r 0 = ⟨(q b).1, a • (q b).2⟩ := by
      exact hr0.trans (congrArg
        (fun s => (⟨(q s).1, a • (q s).2⟩ : Phase S))
        (by ring : a * 0 + b = b))
    change q b = ⟨(r (a⁻¹ * b + -a⁻¹ * b)).1,
      a⁻¹ • (r (a⁻¹ * b + -a⁻¹ * b)).2⟩
    rw [htime, hr0']
    dsimp only
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  obtain ⟨hsub, heq⟩ := maximal_contains_from_spray C G hbridge hq hback ⟨hb, hbL⟩ hmeet
  have htime (t : ℝ) : a⁻¹ * (a * t + b) + -a⁻¹ * b = t := by
    field_simp
    <;> ring
  have hin (t : ℝ) (ht : t ∈ K.carrier) : a * t + b ∈ L.carrier := by
    change a⁻¹ * (a * t + b) + -a⁻¹ * b ∈ K.carrier
    simpa only [htime] using ht
  refine ⟨fun t ht => hsub (hin t ht), ?_⟩
  intro t ht
  have h := heq (hin t ht)
  have hphase := congrArg (fun z : Phase S => (⟨z.1, a • z.2⟩ : Phase S)) h
  change affineCurve S q a b t =
    ⟨(r (a⁻¹ * (a * t + b) + -a⁻¹ * b)).1,
      a • (a⁻¹ • (r (a⁻¹ * (a * t + b) + -a⁻¹ * b)).2)⟩ at hphase
  rw [htime, smul_smul, mul_inv_cancel₀ ha, one_smul] at hphase
  exact hphase

theorem zero_maximal_from_spray (p : M) :
    IsMaximalThrough S C ⟨p, 0⟩ D13Unified.OpenTimeInterval.whole (constantCurve S p) := by
  refine ⟨mem_univ _, rfl, constant_is_geodesic C p, ?_⟩
  intro J q h0 hi hq
  refine ⟨subset_univ _, ?_⟩
  intro t ht
  exact overlap_unique_from_spray C G hbridge D13Unified.OpenTimeInterval.whole J
    (constantCurve S p) q (constant_is_geodesic C p) hq 0 ⟨mem_univ _, h0⟩ hi.symm
      ⟨mem_univ _, ht⟩

end SprayBridge

section Targets

theorem spray_exists :
    P202Specs.Geometry.GeodesicIVP.spray_existsType.{u} := by
  intro n M _ S C
  obtain ⟨X, hX⟩ := spray_section_exists C
  let G := sprayFieldOfCoordinates C X hX (sprayCoordinateFunction_smooth C)
  have hG : HasSprayCoordinates S C G :=
    sprayFieldOfCoordinates_coordinates C X hX (sprayCoordinateFunction_smooth C)
  exact ⟨G, hG, integralCurve_iff_geodesic C G hG⟩

theorem maximal_exists :
    P202Specs.Geometry.GeodesicIVP.maximal_existsType.{u} := by
  intro n M _ S g C _hC w
  obtain ⟨G, _hG, hbridge⟩ := spray_exists S C
  exact maximal_exists_from_spray C G hbridge w

theorem overlap_unique :
    P202Specs.Geometry.GeodesicIVP.overlap_uniqueType.{u} := by
  intro n M _ S C I J q r hq hr s hs hmeet
  obtain ⟨G, _hG, hbridge⟩ := spray_exists S C
  exact overlap_unique_from_spray C G hbridge I J q r hq hr s hs hmeet

theorem domain_open_smooth :
    P202Specs.Geometry.GeodesicIVP.domain_open_smoothType.{u} := by
  intro n M _ S C F hF
  obtain ⟨G, _hG, hbridge⟩ := spray_exists S C
  exact domain_open_smooth_from_spray C G hbridge F hF

theorem maximal_affine :
    P202Specs.Geometry.GeodesicIVP.maximal_affineType.{u} := by
  intro n M _ S C w I q hq a b ha hb
  obtain ⟨G, _hG, hbridge⟩ := spray_exists S C
  exact maximal_affine_from_spray C G hbridge hq a b ha hb

theorem zero_maximal :
    P202Specs.Geometry.GeodesicIVP.zero_maximalType.{u} := by
  intro n M _ S C p
  obtain ⟨G, _hG, hbridge⟩ := spray_exists S C
  exact zero_maximal_from_spray C G hbridge p


theorem constant_speed :
    P202Specs.Geometry.GeodesicIVP.constant_speedType.{u} := by
  intro n M _ S g C hC I q hq s hs t ht
  exact speed_is_constant g C hC I q hq hs ht

theorem coordinate_equation :
    P202Specs.Geometry.GeodesicIVP.coordinate_equationType.{u} := by
  intro n M _ S C I q hq t ht c hp
  exact geodesic_coordinate_equation C hq ht c hp

theorem affine_geodesic :
    P202Specs.Geometry.GeodesicIVP.affine_geodesicType.{u} := by
  intro n M _ S C I q a b hq
  exact geodesic_affine C a b hq

theorem maximal_unique :
    P202Specs.Geometry.GeodesicIVP.maximal_uniqueType.{u} := by
  intro n M _ S C w I J q r hq hr
  exact maximal_unique_of_universal_property C hq hr

theorem constant_geodesic :
    P202Specs.Geometry.GeodesicIVP.constant_geodesicType.{u} := by
  intro n M _ S C p
  exact constant_is_geodesic C p

end Targets
end P202.Geometry.GeodesicIVP
