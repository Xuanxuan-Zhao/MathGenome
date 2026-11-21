import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialJacobi
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiIVP
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiVariation
/-! Conditional draft for G17. No implementation of JacobiVariation is imported.
Every submitted target helper has the eight frozen premises, in contract order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedVariables false

namespace P202.Geometry.ExponentialJacobi
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.ExponentialData P202.ExponentialJacobiData
open Set Filter
open scoped SmoothManifolds.BoundaryConeData
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Linearity of the zero extension; outside the interval all its values are zero. -/
noncomputable def extensionLinearMap (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) :
    RestrictedField S I q →ₗ[ℝ] ((t : ℝ) → TangentSpace S (q t).1) where
  toFun := extendField S I q
  map_add' J K := by
    classical
    funext t
    change extendField S I q (J + K) t = extendField S I q J t + extendField S I q K t
    by_cases ht : t ∈ I.carrier <;> simp [extendField, ht]
  map_smul' c J := by
    classical
    funext t
    change extendField S I q (c • J) t = c • extendField S I q J t
    by_cases ht : t ∈ I.carrier <;> simp [extendField, ht]

@[simp] theorem extendField_at (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (J : RestrictedField S I q) (t : I.carrier) : extendField S I q J t.val = J t := by
  classical
  simp only [extendField, dite_eq_left t.property]

/-- The ambient extension satisfies the equation exactly on the open interval. -/
theorem section_extension (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    {J : RestrictedField S I q} (hJ : IsJacobiSection S C R I q J) :
    IsJacobiField C R I.carrier q (extendField S I q J) := by
  obtain ⟨K, hK, heq⟩ := hJ
  exact JacobiIVP.jacobi_congr C R I.isOpen
    (fun t ht => (heq ⟨t, ht⟩).trans (extendField_at I q J ⟨t, ht⟩).symm) hK

/-- The zero solution needs no curvature representation hypothesis. -/
theorem zero_jacobi (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : Set ℝ) (q : ℝ → Phase S) (hq : IsGeodesicOn S C I q) :
    IsJacobiField C R I q (fun _ => 0) := by
  refine ⟨fun _ => 0, ?_⟩
  intro t ht
  have hzero : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) t 0 := by
    simpa only [zero_smul] using
      CurveCovariantDerivative.derivative_const_smul C (hq t ht).2 (0 : ℝ)
  refine ⟨hzero, ?_⟩
  simpa only [map_zero, LinearMap.zero_apply, neg_zero] using hzero

/-- Actual endpoint solutions form a submodule before taking any span. -/
noncomputable def jacobiEndpointSubmodule (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (a b : I.carrier) :
    Submodule ℝ (RestrictedField S I q) where
  carrier := EndpointFields S C R I q a b
  zero_mem' := ⟨⟨fun _ => 0, zero_jacobi C R I.carrier q hq, fun _ => rfl⟩, rfl, rfl⟩
  add_mem' := by
    rintro J K ⟨⟨J', hJ, hJeq⟩, hJa, hJb⟩ ⟨⟨K', hK, hKeq⟩, hKa, hKb⟩
    refine ⟨⟨fun t => J' t + K' t, JacobiIVP.jacobi_add C R hJ hK, ?_⟩, ?_, ?_⟩
    · intro t
      change J' t.val + K' t.val = J t + K t
      rw [hJeq t, hKeq t]
    · change J a + K a = 0
      rw [hJa, hKa, add_zero]
    · change J b + K b = 0
      rw [hJb, hKb, add_zero]
  smul_mem' := by
    rintro c J ⟨⟨J', hJ, hJeq⟩, hJa, hJb⟩
    refine ⟨⟨fun t => c • J' t, JacobiIVP.jacobi_smul C R hJ c, ?_⟩, ?_, ?_⟩
    · intro t
      change c • J' t.val = c • J t
      rw [hJeq t]
    · change c • J a = 0
      rw [hJa, smul_zero]
    · change c • J b = 0
      rw [hJb, smul_zero]

theorem endpointSpace_eq (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (a b : I.carrier) :
    endpointSpace S C R I q a b = jacobiEndpointSubmodule C R I q hq a b :=
  Submodule.span_eq (jacobiEndpointSubmodule C R I q hq a b)

theorem endpoint_mem_iff (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (a b : I.carrier) (J : RestrictedField S I q) :
    J ∈ endpointSpace S C R I q a b ↔ J ∈ EndpointFields S C R I q a b := by
  rw [endpointSpace_eq C R I q hq a b]
  rfl

/-- The derivative used in the initial jet is an actual covariant derivative. -/
theorem endpoint_derivative (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (a b t : I.carrier)
    (J : endpointSpace S C R I q a b) :
    HasCovariantDerivativeAt C (fun s => (q s).1) (extendField S I q J.val) t.val
      (covariantDerivative C (fun s => (q s).1) (extendField S I q J.val) t.val) := by
  have hJ := ((endpoint_mem_iff C R I q hq a b J.val).mp J.property).1
  obtain ⟨V, hV⟩ := section_extension C R I q hJ
  exact CurveCovariantDerivative.covariantDerivativeWithin_spec C ⟨V t.val, (hV t.val t.property).1⟩

/-- Initial values of the field and its covariant derivative as a linear map. -/
noncomputable def endpointJet (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (a b : I.carrier) :
    endpointSpace S C R I q a b →ₗ[ℝ]
      TangentSpace S (q a.val).1 × TangentSpace S (q a.val).1 where
  toFun J := ⟨J.val a, covariantDerivative C (fun t => (q t).1) (extendField S I q J.val) a.val⟩
  map_add' J K := by
    apply Prod.ext
    · rfl
    · have hd := CurveCovariantDerivative.derivative_add C (mem_univ a.val)
        uniqueDiffWithinAt_univ (endpoint_derivative C R I q hq a b a J)
        (endpoint_derivative C R I q hq a b a K)
      have hext : extendField S I q (J + K).val =
          fun t => extendField S I q J.val t + extendField S I q K.val t :=
        (extensionLinearMap I q).map_add J.val K.val
      change covariantDerivative C _ (extendField S I q (J + K).val) a.val = _
      rw [hext]
      exact CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ a.val)
        uniqueDiffWithinAt_univ hd
  map_smul' c J := by
    apply Prod.ext
    · rfl
    · have hd := CurveCovariantDerivative.derivative_const_smul C
        (endpoint_derivative C R I q hq a b a J) c
      have hext : extendField S I q (c • J).val =
          fun t => c • extendField S I q J.val t :=
        (extensionLinearMap I q).map_smul c J.val
      change covariantDerivative C _ (extendField S I q (c • J).val) a.val = _
      rw [hext]
      exact CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ a.val)
        uniqueDiffWithinAt_univ hd

/-- Fiber transport preserves every intrinsic coordinate vector. -/
theorem coordinates_cast {p q : M} (h : p = q)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) (hq : q ∈ e.source) (w : TangentSpace S p) :
    (tangentStructure S).fiberCoordinates.equiv e he q hq (castTangent S h w) =
      (tangentStructure S).fiberCoordinates.equiv e he p hp w := by
  subst q
  rfl

/-- Differentiating a straight line in a fiber, in any genuine target chart. -/
theorem fiber_ray_deriv (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v w : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)
    (e d : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (hq : fiberExponential F p v ∈ d.source) :
    let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
    HasDerivAt (fun s : ℝ => (d (fiberExponential F p (v + s • w))).val)
      (fderiv ℝ (fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val)
        (E v) (E w)) 0 := by
  dsimp only
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  have hcd := ExponentialNormalCoordinates.fiberExponential_contDiffAt C F hF
    p e he hp d hd (E v) (by simpa only [E, LinearEquiv.symm_apply_apply] using hv)
    (by simpa only [E, LinearEquiv.symm_apply_apply] using hq)
  have hx : HasDerivAt (fun s : ℝ => E v + s • E w) (E w) 0 := by
    simpa only [one_smul, id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (E w)).const_add (E v)
  have hchain := (hcd.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hx
    (by simp)
  simpa only [Function.comp_def, E, map_add, map_smul, LinearEquiv.symm_apply_apply] using hchain

/-- Continuity of the straight fiber curve in the actual phase topology. -/
theorem fiber_ray_continuous (p : M) (v w : TangentSpace S p) :
    ContinuousAt (fun s : ℝ => (⟨p, v + s • w⟩ : Phase S)) 0 := by
  let e := (selectedChart S p).val
  have he := (selectedChart S p).property.1
  have hp := (selectedChart S p).property.2
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  have h := ExponentialNormalCoordinates.fiberInclusion_continuousAt p e he hp (E v)
  have hx : ContinuousAt (fun s : ℝ => E v + s • E w) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hchain := h.comp_of_eq hx (by simp)
  simpa only [Function.comp_def, E, map_add, map_smul, LinearEquiv.symm_apply_apply] using hchain

/-- The chosen formula is a genuine intrinsic velocity, so its value transforms
correctly into every other target chart. -/
theorem fiber_ray_velocity (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v w : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F) :
    let c := fun s : ℝ => fiberExponential F p (v + s • w)
    let h0 : fiberExponential F p v = c 0 := by simp only [c, zero_smul, add_zero]
    HasVelocityWithinAt S c univ 0 (castTangent S h0 (fiberDifferential S F p v w)) := by
  dsimp only
  let c := fun s : ℝ => fiberExponential F p (v + s • w)
  have h0 : fiberExponential F p v = c 0 := by simp only [c, zero_smul, add_zero]
  let e := (selectedChart S p).val
  let d := (selectedChart S (fiberExponential F p v)).val
  have he := (selectedChart S p).property.1
  have hp := (selectedChart S p).property.2
  have hd := (selectedChart S (fiberExponential F p v)).property.1
  have hq := (selectedChart S (fiberExponential F p v)).property.2
  have hinc := fiber_ray_continuous p v w
  have hcont := (ExponentialNormalCoordinates.exponential_smooth C F hF _ hv).1.comp_of_eq hinc
    (by simp)
  have hq0 : c 0 ∈ d.source := by simpa only [c, zero_smul, add_zero] using hq
  refine ⟨hcont.continuousWithinAt, d, hd, hq0, ?_⟩
  rw [coordinates_cast h0 d hd hq hq0]
  have hdif : (tangentStructure S).fiberCoordinates.equiv d hd (fiberExponential F p v) hq
      (fiberDifferential S F p v w) =
      fderiv ℝ (fun x : Euclidean n =>
        (d (fiberExponential F p ((selectedCoordinates S p).symm x))).val)
        (selectedCoordinates S p v) (selectedCoordinates S p w) := by
    simp only [fiberDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearMap.coe_coe, selectedCoordinates, LinearEquiv.apply_symm_apply, d]
  rw [hdif]
  exact (fiber_ray_deriv C F hF p v w hv e d he hd hp hq).hasDerivWithinAt

/-- IVP uniqueness makes the initial-jet map injective on the restricted space. -/
theorem endpointJet_injective
    (hivp : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (a b : I.carrier) :
    Function.Injective (endpointJet C R I q hq a b) := by
  intro J K heq
  have hval := congrArg Prod.fst heq
  have hder := congrArg Prod.snd heq
  change J.val a = K.val a at hval
  change covariantDerivative C (fun s => (q s).1) (extendField S I q J.val) a.val =
    covariantDerivative C (fun s => (q s).1) (extendField S I q K.val) a.val at hder
  have hJ := ((endpoint_mem_iff C R I q hq a b J.val).mp J.property).1
  have hK := ((endpoint_mem_iff C R I q hq a b K.val).mp K.property).1
  obtain ⟨W, hW, hW0, hWd, huniq⟩ := hivp S g C hC R hR I q hq a.val a.property
    (J.val a) (covariantDerivative C (fun s => (q s).1) (extendField S I q J.val) a.val)
  have hJeq := huniq (extendField S I q J.val) (section_extension C R I q hJ)
    (extendField_at I q J.val a) (endpoint_derivative C R I q hq a b a J)
  have hKd := endpoint_derivative C R I q hq a b a K
  rw [← hder] at hKd
  have hKeq := huniq (extendField S I q K.val) (section_extension C R I q hK)
    ((extendField_at I q K.val a).trans hval.symm) hKd
  apply Subtype.ext
  funext t
  exact (extendField_at I q J.val t).symm.trans
    ((hJeq t.val t.property).trans ((hKeq t.val t.property).symm.trans (extendField_at I q K.val t)))

/-- Conjugacy is the existence of a nonzero vector in the genuine endpoint space. -/
theorem conjugate_iff_exists_endpoint (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (a b : I.carrier) :
    ConjugateAlong S C R I q a b ↔ ∃ J : endpointSpace S C R I q a b, J ≠ 0 := by
  constructor
  · rintro ⟨J, hJ, hne⟩
    refine ⟨⟨J, (endpoint_mem_iff C R I q hq a b J).mpr hJ⟩, ?_⟩
    intro hz
    exact hne (congrArg Subtype.val hz)
  · rintro ⟨J, hne⟩
    refine ⟨J.val, (endpoint_mem_iff C R I q hq a b J.val).mp J.property, ?_⟩
    intro hz
    exact hne (Subtype.ext hz)

/-- The transport used in the variation interface is ordinary fiber transport. -/
theorem phase_transport (x y : Phase S) (h : x = y) (w : TangentSpace S y.1) :
    Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) h).symm w =
      castTangent S (congrArg Sigma.fst h).symm w := by
  subst y
  rfl

/-- With stationary base position, the covariant fiber derivative is the
ordinary velocity-coordinate derivative. No mixed derivative is needed. -/
theorem stationary_phase_jet (C : Connection (tangentBundle S))
    (r : ℝ → Phase S) (D : TangentSpace S (r 0).1)
    (hpos : HasVelocityWithinAt S (fun s => (r s).1) univ 0 0)
    (hD : HasCovariantDerivativeAt C (fun s => (r s).1) (fun s => (r s).2) 0 D)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : (r 0).1 ∈ e.source) :
    HasDerivAt (fun s => (((tangentStructure S).chart e he) (r s)).val)
      ((tangentStructure S).productCoordinates.linearEquiv
        (0, (tangentStructure S).fiberCoordinates.equiv e he (r 0).1 hp D)) 0 := by
  let c : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e, he⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hpB : (r 0).1 ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hp
  obtain ⟨a, ha⟩ := CurveCovariantDerivative.exists_coefficients_deriv C (mem_univ 0) hD b hpB
  have hformula := CurveCovariantDerivative.local_formula C (mem_univ 0) uniqueDiffWithinAt_univ
    hD b hpB hpos ha
  have hcoord : (tangentStructure S).fiberCoordinates.equiv e he (r 0).1 hp D = a := by
    have hequiv : (b.basis ⟨(r 0).1, hpB⟩).equivFun D = a := by
      have hz : connectionMatrix C b ⟨(r 0).1, hpB⟩ 0 = 0 := by
        ext i j
        exact (connectionForm C b ⟨(r 0).1, hpB⟩ i j).map_zero
      rw [hformula]
      simp only [frameDerivative, LinearEquiv.apply_symm_apply, hz,
        Matrix.zero_mulVec, add_zero]
    rw [GeodesicIVP.trivializationFrame_equivFun] at hequiv
    change (((tangentBundle S).trivialization c) ⟨(r 0).1, D⟩).2 = a at hequiv
    rw [(tangentRealization S).coordinates c (r 0).1 hp D] at hequiv
    exact hequiv
  have hx := CurveCovariantDerivative.velocity_coordinates hpos (mem_univ 0) e he hp
  have hv : HasDerivAt (chartVelocity S c r)
      ((tangentStructure S).fiberCoordinates.equiv e he (r 0).1 hp D) 0 := by
    rw [hcoord]
    exact hasDerivWithinAt_univ.mp ha
  exact GeodesicIVP.phase_chart_hasDerivAt c r 0 hp (hpos.1.continuousAt (by simp))
    (by simpa only [map_zero] using (hasDerivWithinAt_univ.mp hx)) hv

/-- The straight initial-velocity curve has exactly the same vertical jet. -/
theorem fiber_ray_phase_jet (p : M) (v w : TangentSpace S p)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    HasDerivAt (fun s : ℝ => (((tangentStructure S).chart e he) ⟨p, v + s • w⟩).val)
      ((tangentStructure S).productCoordinates.linearEquiv
        (0, (tangentStructure S).fiberCoordinates.equiv e he p hp w)) 0 := by
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let c : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e, he⟩
  have hv : HasDerivAt (fun s : ℝ => E v + s • E w) (E w) 0 := by
    simpa only [one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (E w)).const_add (E v)
  have heq : (chartVelocity S c (fun s : ℝ => ⟨p, v + s • w⟩)) =
      (fun s : ℝ => E v + s • E w) := by
    funext s
    rw [GeodesicIVP.chartVelocity_eq c _ s hp]
    exact E.map_add v (s • w) |>.trans (congrArg (fun z => E v + z) (E.map_smul s w))
  exact GeodesicIVP.phase_chart_hasDerivAt c (fun s : ℝ => (⟨p, v + s • w⟩ : Phase S)) 0 hp continuousAt_const
    (hasDerivAt_const (0 : ℝ) (e p).val) (heq ▸ hv)

/-- The differential of a smooth flow slice depends only on the initial jet.
The statement uses the actual time/phase survival domain. -/
theorem flow_slice_equal_jets (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (t : ℝ) (z : Phase S)
    (ht : (t, z) ∈ flowDomain F)
    (e : ModelChart (n + n) .euclidean (Phase S))
    (he : e ∈ (phaseManifold S).smoothStructure.val) (hz : z ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hdt : (F.curve z t).1 ∈ d.source)
    (r k : ℝ → Phase S) (hr : ContinuousAt r 0) (hk : ContinuousAt k 0)
    (hr0 : r 0 = z) (hk0 : k 0 = z) (a : Euclidean (n + n))
    (hra : HasDerivAt (fun s => (e (r s)).val) a 0)
    (hka : HasDerivAt (fun s => (e (k s)).val) a 0) :
    ∃ L : Euclidean n,
      HasDerivAt (fun s => (d (F.curve (r s) t).1).val) L 0 ∧
      HasDerivAt (fun s => (d (F.curve (k s) t).1).val) L 0 := by
  obtain ⟨U, hU, hzU, H, hH, heq⟩ :=
    ((GeodesicIVP.domain_open_smooth S C F hF).2 (t, z) ht).2.2 e he d hd hz hdt
  have hf := (hH.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
  refine ⟨fderiv ℝ H (t, (e z).val) (0, a), ?_, ?_⟩
  · have hj := (hasDerivAt_const (0 : ℝ) t).prodMk hra
    have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hj (by simp only [hr0])
    have hc : ContinuousAt (fun s => (t, r s)) 0 := continuousAt_const.prodMk hr
    have hcomp := heq.comp_tendsto (by simpa only [ContinuousAt, hr0] using hc)
    exact hh.congr_of_eventuallyEq hcomp.symm
  · have hj := (hasDerivAt_const (0 : ℝ) t).prodMk hka
    have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hj (by simp only [hk0])
    have hc : ContinuousAt (fun s => (t, k s)) 0 := continuousAt_const.prodMk hk
    have hcomp := heq.comp_tendsto (by simpa only [ContinuousAt, hk0] using hc)
    exact hh.congr_of_eventuallyEq hcomp.symm

/-- Transport across an equality of base points changes no intrinsic vector. -/
theorem castTangent_heq {p q : M} (h : p = q) (w : TangentSpace S p) :
    HEq (castTangent S h w) w := by
  subst q
  rfl

/-- Realization supplies precisely the vertical initial jet needed to
identify the exponential differential, without assuming completeness. -/
theorem differential_formula_of_realization
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u}) :
    P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u} := by
  intro n M _ S g C hC R hR F hF p v w J hJ hJ0 hJd t ht
  let I := F.interval ⟨p, v⟩
  let q := F.curve ⟨p, v⟩
  have h0 : 0 ∈ I.carrier := (hF ⟨p, v⟩).1
  have hgeo : IsGeodesicOn S C I.carrier q := (hF ⟨p, v⟩).2.2.1
  have hseg : Icc t t ⊆ I.carrier := by
    intro s hs
    have hs' : s = t := le_antisymm hs.2 hs.1
    simpa only [hs'] using ht
  obtain ⟨U, hU, hsegU, hU0, hUI, V, hVJ, hjet, hcont, hflow⟩ :=
    hreal S g C hC R hR I q hgeo J hJ 0 h0
      (initialIdentification S C F hF p v w) hJd t t le_rfl hseg F hF
  have htU : t ∈ U := hsegU ⟨le_rfl, le_rfl⟩
  let r : ℝ → Phase S := fun s => V.phase (s, 0)
  let k : ℝ → Phase S := fun s => ⟨p, v + s • w⟩
  let e := (selectedChart S p).val
  have he := (selectedChart S p).property.1
  have hp := (selectedChart S p).property.2
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let b := (tangentStructure S).chart e he
  have hb := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
  have hinit : r 0 = (⟨p, v⟩ : Phase S) := (V.central 0).trans (hF ⟨p, v⟩).2.1
  have hk0 : k 0 = (⟨p, v⟩ : Phase S) := by simp only [k, zero_smul, add_zero]
  have hpq0 : (q 0).1 ∈ e.source := by
    change (F.curve ⟨p, v⟩ 0).1 ∈ e.source
    rw [(hF ⟨p, v⟩).2.1]
    exact hp
  have hpr0 : (r 0).1 ∈ e.source := by rw [hinit]; exact hp
  have hpos : HasVelocityWithinAt S (fun s => (r s).1) univ 0 0 := by
    have hh := hVJ 0 hU0
    rw [phase_transport (V.phase (0, 0)) (q 0) (V.central 0) (J 0)] at hh
    simpa only [hJ0, map_zero] using hh
  let D := castTangent S (congrArg Sigma.fst (V.central 0)).symm
    (initialIdentification S C F hF p v w)
  have hD : HasCovariantDerivativeAt C (fun s => (r s).1) (fun s => (r s).2) 0 D := by
    change HasCovariantDerivativeAt C (fun s => (V.phase (s, 0)).1)
      (fun s => (V.phase (s, 0)).2) 0
      (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) (V.central 0)).symm
        (initialIdentification S C F hF p v w)) at hjet
    rw [phase_transport (V.phase (0, 0)) (q 0) (V.central 0)
      (initialIdentification S C F hF p v w)] at hjet
    exact hjet
  have hDcoord : (tangentStructure S).fiberCoordinates.equiv e he (r 0).1 hpr0 D = E w := by
    exact (coordinates_cast (congrArg Sigma.fst (V.central 0)).symm e he hpq0 hpr0
      (initialIdentification S C F hF p v w)).trans
      (coordinates_cast (congrArg Sigma.fst (hF ⟨p, v⟩).2.1).symm e he hp hpq0 w)
  have hrjet := stationary_phase_jet C r D hpos hD e he hpr0
  rw [hDcoord] at hrjet
  have hkjet := fiber_ray_phase_jet p v w e he hp
  have hbs : (⟨p, v⟩ : Phase S) ∈ b.source := by
    simpa only [b, (tangentStructure S).chart_source,
      SmoothManifolds.TangentBundleData.projection, mem_preimage] using hp
  have hrad := ExponentialNormalCoordinates.radial_identity_at C F hF p v t ht
  let y := fiberExponential F p (t • v)
  let d := (selectedChart S y).val
  have hd := (selectedChart S y).property.1
  have hyd := (selectedChart S y).property.2
  have hdt : (q t).1 ∈ d.source := hrad.2 ▸ hyd
  obtain ⟨L, hLr, hLk⟩ := flow_slice_equal_jets C F hF t ⟨p, v⟩ ht b hb hbs d hd hdt
    r k hcont (fiber_ray_continuous p v w) hinit hk0
    ((tangentStructure S).productCoordinates.linearEquiv (0, E w)) hrjet hkjet
  have hwidth : Ioo (-V.width) V.width ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩
  have hvarEq : (fun s : ℝ => (d (V.phase (s, t)).1).val) =ᶠ[𝓝 0]
      (fun s => (d (F.curve (r s) t).1).val) := by
    filter_upwards [hwidth] with s hs
    have hh := (hflow s hs t htU).2
    simpa only [sub_zero] using congrArg (fun z : Phase S => (d z.1).val) hh
  have hvarDer := hLr.congr_of_eventuallyEq hvarEq
  have hpvar : (V.phase (0, t)).1 ∈ d.source := by rw [V.central t]; exact hdt
  have hJdt := CurveCovariantDerivative.velocity_coordinates (hVJ t htU) (mem_univ 0) d hd hpvar
  rw [phase_transport (V.phase (0, t)) (q t) (V.central t) (J t),
    coordinates_cast (congrArg Sigma.fst (V.central t)).symm d hd hdt hpvar] at hJdt
  have hJcoord : (tangentStructure S).fiberCoordinates.equiv d hd (q t).1 hdt (J t) = L :=
    (hasDerivWithinAt_univ.mp hJdt).unique hvarDer
  have hkcont : ContinuousAt (fun s : ℝ => (t, k s)) 0 :=
    continuousAt_const.prodMk (fiber_ray_continuous p v w)
  have hkdom : ∀ᶠ s in 𝓝 (0 : ℝ), (t, k s) ∈ flowDomain F := by
    apply hkcont.preimage_mem_nhds
    apply (GeodesicIVP.domain_open_smooth S C F hF).1.mem_nhds
    simpa only [flowDomain, mem_ofPred_eq, hk0] using ht
  have hExpEq : (fun s : ℝ => (d (fiberExponential F p (t • v + s • (t • w)))).val) =ᶠ[𝓝 0]
      (fun s => (d (F.curve (k s) t).1).val) := by
    filter_upwards [hkdom] with s hs
    have hh := (ExponentialNormalCoordinates.radial_identity_at C F hF p (v + s • w) t hs).2
    have halg : t • (v + s • w) = t • v + s • (t • w) := by
      simp only [smul_add, smul_smul, mul_comm t s]
    rw [halg] at hh
    exact congrArg (fun z : M => (d z).val) hh
  have hExpDer := hLk.congr_of_eventuallyEq hExpEq
  have hRay := fiber_ray_deriv C F hF p (t • v) (t • w) hrad.1 e d he hd hp hyd
  have hDiffcoord : (tangentStructure S).fiberCoordinates.equiv d hd y hyd
      (fiberDifferential S F p (t • v) (t • w)) =
      fderiv ℝ (fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val)
        (E (t • v)) (E (t • w)) := by
    simp only [fiberDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearMap.coe_coe, selectedCoordinates, LinearEquiv.apply_symm_apply, d, E, e, y]
  have hDcoordL : (tangentStructure S).fiberCoordinates.equiv d hd y hyd
      (fiberDifferential S F p (t • v) (t • w)) = L :=
    hDiffcoord.trans (hRay.unique hExpDer)
  have heq : J t = castTangent S hrad.2 (fiberDifferential S F p (t • v) (t • w)) := by
    apply ((tangentStructure S).fiberCoordinates.equiv d hd (q t).1 hdt).injective
    rw [coordinates_cast hrad.2 d hd hyd hdt]
    exact hJcoord.trans hDcoordL.symm
  exact (heq_of_eq heq).trans (castTangent_heq hrad.2 _)

/-- The derivative initial datum of a two-endpoint field lies in the
exponential kernel after multiplication by the nonzero endpoint time. -/
theorem endpoint_differential_zero
    (hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p) (t : ℝ) (ht : t ∈ (F.interval ⟨p, v⟩).carrier)
    (J : endpointSpace S C R (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩)
      ⟨0, (hF ⟨p, v⟩).1⟩ ⟨t, ht⟩) :
    fiberDifferential S F p (t • v)
      (t • (initialIdentification S C F hF p v).symm
        (covariantDerivative C (fun s => (F.curve ⟨p, v⟩ s).1)
          (extendField S (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩) J.val) 0)) = 0 := by
  let I := F.interval ⟨p, v⟩
  let q := F.curve ⟨p, v⟩
  let a : I.carrier := ⟨0, (hF ⟨p, v⟩).1⟩
  let b : I.carrier := ⟨t, ht⟩
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v⟩).2.2.1
  have hmem := (endpoint_mem_iff C R I q hq a b J.val).mp J.property
  let W := extendField S I q J.val
  let w0 := covariantDerivative C (fun s => (q s).1) W 0
  let w := (initialIdentification S C F hF p v).symm w0
  have hW : IsJacobiField C R I.carrier q W := section_extension C R I q hmem.1
  have hW0 : W 0 = 0 := (extendField_at I q J.val a).trans hmem.2.1
  have hWd : HasCovariantDerivativeAt C (fun s => (q s).1) W 0
      (initialIdentification S C F hF p v w) := by
    simpa only [w, LinearEquiv.apply_symm_apply] using endpoint_derivative C R I q hq a b a J
  have hWend : W t = 0 := (extendField_at I q J.val b).trans hmem.2.2
  have hf := hformula S g C hC R hR F hF p v w W hW hW0 hWd t ht
  have hrad := (ExponentialNormalCoordinates.radial_identity_at C F hF p v t ht).2
  have heq : castTangent S hrad (fiberDifferential S F p (t • v) (t • w)) = W t :=
    eq_of_heq ((castTangent_heq hrad _).trans hf.symm)
  have hz := heq.trans hWend
  exact (castTangent S hrad).injective (hz.trans (map_zero (castTangent S hrad)).symm)

/-- The concrete map sends a field to t times its initial covariant derivative,
using the canonical initial fiber identification. -/
noncomputable def endpointKernelMap
    (hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p) (t : ℝ) (ht : t ∈ (F.interval ⟨p, v⟩).carrier) :
    endpointSpace S C R (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩)
      ⟨0, (hF ⟨p, v⟩).1⟩ ⟨t, ht⟩ →ₗ[ℝ]
      LinearMap.ker (fiberDifferential S F p (t • v)) := by
  let I := F.interval ⟨p, v⟩
  let q := F.curve ⟨p, v⟩
  let a : I.carrier := ⟨0, (hF ⟨p, v⟩).1⟩
  let b : I.carrier := ⟨t, ht⟩
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v⟩).2.2.1
  let L := (t • (initialIdentification S C F hF p v).symm.toLinearMap).comp
    ((LinearMap.snd ℝ (TangentSpace S (q 0).1) (TangentSpace S (q 0).1)).comp
      (endpointJet C R I q hq a b))
  exact L.codRestrict _ (endpoint_differential_zero hformula g C hC R hR F hF p v t ht)

theorem endpointKernelMap_apply
    (hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p) (t : ℝ) (ht : t ∈ (F.interval ⟨p, v⟩).carrier)
    (J : endpointSpace S C R (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩)
      ⟨0, (hF ⟨p, v⟩).1⟩ ⟨t, ht⟩) :
    (endpointKernelMap hformula g C hC R hR F hF p v t ht J).val =
      t • (initialIdentification S C F hF p v).symm
        (covariantDerivative C (fun s => (F.curve ⟨p, v⟩ s).1)
          (extendField S (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩) J.val) 0) := rfl

/-- Conversely, IVP existence with initial derivative k/t realizes each
kernel vector as a two-endpoint field, on the original maximal interval. -/
theorem endpointKernelMap_bijective
    (hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (hivp : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p) (t : ℝ) (ht0 : 0 < t)
    (ht : t ∈ (F.interval ⟨p, v⟩).carrier) :
    Function.Bijective (endpointKernelMap hformula g C hC R hR F hF p v t ht) := by
  let I := F.interval ⟨p, v⟩
  let q := F.curve ⟨p, v⟩
  let a : I.carrier := ⟨0, (hF ⟨p, v⟩).1⟩
  let b : I.carrier := ⟨t, ht⟩
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v⟩).2.2.1
  let E := initialIdentification S C F hF p v
  have htne : t ≠ 0 := ne_of_gt ht0
  constructor
  · intro J K heq
    have hvalues := congrArg Subtype.val heq
    rw [endpointKernelMap_apply, endpointKernelMap_apply] at hvalues
    have hder := E.symm.injective ((smul_right_injective _ htne) hvalues)
    apply endpointJet_injective hivp g C hC R hR I q hq a b
    apply Prod.ext
    · have hJa := ((endpoint_mem_iff C R I q hq a b J.val).mp J.property).2.1
      have hKa := ((endpoint_mem_iff C R I q hq a b K.val).mp K.property).2.1
      exact hJa.trans hKa.symm
    · exact hder
  · intro k
    let w := t⁻¹ • k.val
    obtain ⟨J, hJ, hJ0, hJd, huniq⟩ := hivp S g C hC R hR I q hq 0 a.property 0 (E w)
    have hform := hformula S g C hC R hR F hF p v w J hJ hJ0 hJd t ht
    have hscale : t • w = k.val := by
      simp only [w, smul_smul, mul_inv_cancel₀ htne, one_smul]
    have hrad := (ExponentialNormalCoordinates.radial_identity_at C F hF p v t ht).2
    have hzero : fiberDifferential S F p (t • v) (t • w) = 0 := by
      rw [hscale]
      exact k.property
    have hJt : J t = 0 := by
      have hh : J t = castTangent S hrad (fiberDifferential S F p (t • v) (t • w)) :=
        eq_of_heq (hform.trans (castTangent_heq hrad _).symm)
      simpa only [hzero, map_zero] using hh
    let Jres : RestrictedField S I q := fun s => J s.val
    have hJmem : Jres ∈ EndpointFields S C R I q a b :=
      ⟨⟨J, hJ, fun _ => rfl⟩, hJ0, hJt⟩
    let Jspace : endpointSpace S C R I q a b :=
      ⟨Jres, (endpoint_mem_iff C R I q hq a b Jres).mpr hJmem⟩
    refine ⟨Jspace, ?_⟩
    apply Subtype.ext
    rw [endpointKernelMap_apply]
    have hJeq : ∀ᶠ s in 𝓝 (0 : ℝ), J s = extendField S I q Jres s := by
      filter_upwards [I.isOpen.mem_nhds a.property] with s hs
      exact (extendField_at I q Jres ⟨s, hs⟩).symm
    have hD := ParallelTransport.derivative_field_congr C (mem_univ 0)
      (by simpa only [nhdsWithin_univ] using hJeq) hJd
    have hdval := CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ 0)
      uniqueDiffWithinAt_univ hD
    change t • E.symm (covariantDerivative C (fun s => (q s).1)
      (extendField S I q Jres) 0) = k.val
    dsimp only [covariantDerivative]
    rw [hdval, LinearEquiv.symm_apply_apply]
    exact hscale

theorem differential_zero_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u} := by
  exact ExponentialNormalCoordinates.derivative_zero

theorem endpoint_space_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u} := by
  intro n M _ S C R I q hq a b J
  exact endpoint_mem_iff C R I q hq a b J

theorem two_zeros_normal_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u} := by
  intro n M _ S g C hC R hR I q hq hn J hJ a ha b hb hab hJa hJb t ht
  obtain ⟨⟨A, B, htan⟩, _, _, hnormal⟩ := hdecomp S g C hC R hR I q hq hn J hJ
  have hza : (A + B * a) • (q a).2 = 0 := by
    rw [← htan a ha]
    simp [P202.JacobiData.tangentialPart, hJa, pairing]
  have hzb : (A + B * b) • (q b).2 = 0 := by
    rw [← htan b hb]
    simp [P202.JacobiData.tangentialPart, hJb, pairing]
  have hA : A + B * a = 0 := (smul_eq_zero.mp hza).resolve_right
    (JacobiIVP.velocity_ne_zero C I q hq hn a ha)
  have hB : A + B * b = 0 := (smul_eq_zero.mp hzb).resolve_right
    (JacobiIVP.velocity_ne_zero C I q hq hn b hb)
  have hB0 : B = 0 := by
    have hz : B * (a - b) = 0 := by nlinarith [hA, hB]
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hab)
  have hA0 : A = 0 := by simpa only [hB0, zero_mul, add_zero] using hA
  have htan0 : P202.JacobiData.tangentialPart g q J t = 0 := by
    rw [htan t ht, hA0, hB0, zero_mul, zero_add, zero_smul]
  have heq : P202.JacobiData.normalPart g q J t = J t := by
    simp only [P202.JacobiData.normalPart, htan0, sub_zero]
  rw [← heq]
  exact hnormal t ht

theorem differential_coordinates_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u} := by
  intro n M _ S C F hF p v hv e d he hd hp hq
  dsimp only
  intro w
  let c := fun s : ℝ => fiberExponential F p (v + s • w)
  have h0 : fiberExponential F p v = c 0 := by simp only [c, zero_smul, add_zero]
  have hq0 : c 0 ∈ d.source := h0 ▸ hq
  have hvel : HasVelocityWithinAt S c univ 0
      (castTangent S h0 (fiberDifferential S F p v w)) := fiber_ray_velocity C F hF p v w hv
  have hleft := CurveCovariantDerivative.velocity_coordinates hvel (mem_univ 0) d hd hq0
  rw [coordinates_cast h0 d hd hq hq0] at hleft
  have hright := fiber_ray_deriv C F hF p v w hv e d he hd hp hq
  exact (hasDerivWithinAt_univ.mp hleft).unique hright

theorem multiplicity_finite_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u} := by
  intro n M _ S g C hC R hR I q hq a b
  let E := selectedCoordinates S (q a.val).1
  letI : FiniteDimensional ℝ (TangentSpace S (q a.val).1) := E.symm.finiteDimensional
  letI : FiniteDimensional ℝ (endpointSpace S C R I q a b) :=
    FiniteDimensional.of_injective (endpointJet C R I q hq a b)
      (endpointJet_injective hexists g C hC R hR I q hq a b)
  refine ⟨inferInstance, ?_⟩
  rw [conjugate_iff_exists_endpoint C R I q hq a b]
  exact Module.finrank_pos_iff_exists_ne_zero.symm

theorem differential_formula_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u} := by
  exact differential_formula_of_realization hreal

theorem kernel_equivalence_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u} := by
  intro n M _ S g C hC R hR F hF p v t ht0 ht
  have hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u} :=
    differential_formula_of_realization hreal
  let e := LinearEquiv.ofBijective (endpointKernelMap hformula g C hC R hR F hF p v t ht)
    (endpointKernelMap_bijective hformula hexists g C hC R hR F hF p v t ht0 ht)
  exact ⟨⟨e⟩, e.finrank_eq⟩

theorem conjugacy_singularity_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u} := by
  intro n M _ S g C hC R hR F hF p v t ht0 ht
  let I := F.interval ⟨p, v⟩
  let q := F.curve ⟨p, v⟩
  let a : I.carrier := ⟨0, (hF ⟨p, v⟩).1⟩
  let b : I.carrier := ⟨t, ht⟩
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v⟩).2.2.1
  let D := fiberDifferential S F p (t • v)
  obtain ⟨⟨E⟩, hdim⟩ := kernel_equivalence_conditional hcompact hdecomp hexists hfamily
    hreal hfieldexists hfieldunique hjacobi S g C hC R hR F hF p v t ht0 ht
  have hfields : (∃ J : endpointSpace S C R I q a b, J ≠ 0) ↔
      ∃ z : LinearMap.ker D, z ≠ 0 := by
    constructor
    · rintro ⟨J, hJ⟩
      refine ⟨E J, ?_⟩
      intro hz
      apply hJ
      apply E.injective
      simpa only [map_zero] using hz
    · rintro ⟨z, hz⟩
      refine ⟨E.symm z, ?_⟩
      intro hJ
      apply hz
      apply E.symm.injective
      simpa only [map_zero] using hJ
  have hker : (∃ z : LinearMap.ker D, z ≠ 0) ↔ ¬ Function.Injective D := by
    constructor
    · rintro ⟨z, hz⟩ hinj
      apply hz
      apply Subtype.ext
      exact hinj (z.property.trans D.map_zero.symm)
    · intro hni
      by_contra hnone
      apply hni
      intro x y hxy
      by_contra hne
      apply hnone
      have hzero : D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      refine ⟨⟨x - y, hzero⟩, ?_⟩
      intro hz
      exact hne (sub_eq_zero.mp (congrArg Subtype.val hz))
  let Ep := selectedCoordinates S p
  let Et := selectedCoordinates S (fiberExponential F p (t • v))
  letI : FiniteDimensional ℝ (TangentSpace S p) := Ep.symm.finiteDimensional
  letI : FiniteDimensional ℝ (TangentSpace S (fiberExponential F p (t • v))) := Et.symm.finiteDimensional
  have hdims : Module.finrank ℝ (TangentSpace S p) =
      Module.finrank ℝ (TangentSpace S (fiberExponential F p (t • v))) :=
    Ep.finrank_eq.trans Et.finrank_eq.symm
  have hsurj := LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdims (f := D)
  have hbi : Function.Bijective D ↔ Function.Injective D :=
    ⟨fun h => h.1, fun h => ⟨h, hsurj.mp h⟩⟩
  exact (conjugate_iff_exists_endpoint C R I q hq a b).trans
    (hfields.trans (hker.trans (not_congr hbi).symm))

theorem radial_field_conditional
    (hcompact : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u})
    (hdecomp : P202Specs.Geometry.JacobiVariation.decompositionType.{u})
    (hexists : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u})
    (hfamily : P202Specs.Geometry.JacobiVariation.family_existsType.{u})
    (hreal : P202Specs.Geometry.JacobiVariation.realizationType.{u})
    (hfieldexists : P202Specs.Geometry.JacobiVariation.variation_field_existsType.{u})
    (hfieldunique : P202Specs.Geometry.JacobiVariation.variation_field_uniqueType.{u})
    (hjacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u})
    : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u} := by
  intro n M _ S g C hC R hR F hF p v w
  obtain ⟨J, hJ, hJ0, hJd, huniq⟩ := hexists S g C hC R hR (F.interval ⟨p, v⟩)
    (F.curve ⟨p, v⟩) (hF ⟨p, v⟩).2.2.1 0 (hF ⟨p, v⟩).1 0
    (initialIdentification S C F hF p v w)
  exact ⟨J, hJ, hJ0, hJd, differential_formula_of_realization hreal S g C hC R hR
    F hF p v w J hJ hJ0 hJd, huniq⟩

end P202.Geometry.ExponentialJacobi

universe v8_closure_80386f8d9da6a0e1_u0
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«conjugacy_singularityType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«differential_coordinatesType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«differential_formulaType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«differential_zeroType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«endpoint_spaceType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«kernel_equivalenceType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«multiplicity_finiteType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«radial_field» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«radial_fieldType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
theorem _root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal» : _root_.«P202Specs».«Geometry».«ExponentialJacobi».«two_zeros_normalType».{v8_closure_80386f8d9da6a0e1_u0} :=
  @_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal_conditional».{v8_closure_80386f8d9da6a0e1_u0} (@_root_.«P202».«Geometry».«JacobiVariation».«compact_survival».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«decomposition».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«exists_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«family_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«realization».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_exists».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_field_unique».{v8_closure_80386f8d9da6a0e1_u0}) (@_root_.«P202».«Geometry».«JacobiVariation».«variation_jacobi».{v8_closure_80386f8d9da6a0e1_u0})
