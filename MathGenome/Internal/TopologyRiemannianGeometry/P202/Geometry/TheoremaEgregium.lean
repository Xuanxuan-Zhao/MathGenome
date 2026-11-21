import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TheoremaEgregium
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussCodazziRicci

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.Geometry.TheoremaEgregium
attribute [local instance] GaussCodazziRicci.sectionAddCommGroup
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GaussWeingartenData
  P202.CurvatureData P202.CurvatureEquationsData P202.EgregiumData
open Filter
open scoped Topology
universe u

/-- Strict Cauchy–Schwarz in the form needed for the first form denominator. -/
theorem gram_pos {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M)
    (v w : TangentSpace S p) (hi : LinearIndependent ℝ ![v, w]) :
    0 < pairing g p v v * pairing g p w w - pairing g p v w ^ 2 := by
  have hv : v ≠ 0 := hi.ne_zero 0
  have ha : 0 < pairing g p v v := g.positive p v hv
  have hn : pairing g p v v • w - pairing g p v w • v ≠ 0 := by
    intro hz
    have his : LinearIndependent ℝ ![w, v] := by
      convert hi.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1).injective using 1
      ext j
      fin_cases j <;> simp
    have hh := (linearIndependent_fin2 (K := ℝ) (f := ![w, v])).mp
      his
    have hh' : ∀ t : ℝ, t • v ≠ w := hh.2
    apply hh' (pairing g p v w / pairing g p v v)
    have he : pairing g p v v • w = pairing g p v w • v := sub_eq_zero.mp hz
    apply (smul_right_injective (TangentSpace S p) ha.ne')
    have hs : pairing g p v v * (pairing g p v w / pairing g p v v) = pairing g p v w := by
      field_simp
    change pairing g p v v • ((pairing g p v w / pairing g p v v) • v) = pairing g p v v • w
    rw [smul_smul, hs]
    exact he.symm
  have hp := g.positive p _ hn
  have hexp : pairing g p (pairing g p v v • w - pairing g p v w • v)
      (pairing g p v v • w - pairing g p v w • v) =
      pairing g p v v * (pairing g p v v * pairing g p w w - pairing g p v w ^ 2) := by
    simp only [LeviCivita.tangent_sub_as_add, smul_smul, pairing, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    have hsymm := g.symmetric p w v
    rw [hsymm]
    ring
  change 0 < pairing g p (pairing g p v v • w - pairing g p v w • v)
    (pairing g p v v • w - pairing g p v w • v) at hp
  rw [hexp] at hp
  exact pos_of_mul_pos_right hp ha.le

theorem firstForm_det_pos : P202Specs.Geometry.TheoremaEgregium.firstForm_det_posType.{u} := by
  intro n a M _ S g p e
  have hi : LinearIndependent ℝ ![e 0, e 1] := by
    convert e.linearIndependent using 1
    ext j
    fin_cases j <;> rfl
  simpa only [firstFormMatrix, Matrix.det_fin_two, pairing, g.symmetric p (e 1) (e 0), pow_two]
    using gram_pos g p (e 0) (e 1) hi


section Cartesian
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable def globalCoordinateField (c : TangentIndex S)
    (hc : ∀ p, p ∈ (tangentBundle S).baseSet c) (j : Fin n) : Field S := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  refine ⟨fun p => coordinateVector c j p, ?_⟩
  have hs := b.smooth j
  have he : (fun p : B.baseSet c =>
      (⟨p.val, b.section_ j p⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) =
      (fun p : B.baseSet c => ⟨p.val, coordinateVector c j p.val⟩) := by
    funext p
    congr 1
    exact LeviCivita.trivializationFrame_section c j p
  rw [he] at hs
  have ht := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    S.smoothStructure.val B.totalManifold.smoothStructure.val
    (fun p => (⟨p, coordinateVector c j p⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S)))
    (B.baseSet c) (B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet)).mpr hs
  exact fun p => ht p (hc p)

theorem scalarDerivative_constant (r : ℝ) (p : M) (v : TangentSpace S p) :
    scalarDerivative S (fun _ => r) p v = 0 := by
  let f : GlobalSmooth S := algebraMap ℝ (GlobalSmooth S) r
  exact (ConnectionForms.scalarDerivative_representative (fun _ => r) f p
    (Eventually.of_forall (fun _ => rfl)) v).trans
    (SmoothManifolds.derivation_kills_constants (germEvaluation S p) v r)

/-- A Cartesian metric has zero curvature, derived from Koszul rather than
included in the definition of the metric. -/
theorem cartesian_curvature_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (c : TangentIndex S) (hc : ∀ p, p ∈ (tangentBundle S).baseSet c)
    (hg : ∀ p, metricMatrix g c p = 1) :
    ∀ p v w z, R.val p v w z = 0 := by
  classical
  let E := globalCoordinateField c hc
  have hE (j : Fin n) (p : M) : (E j).val p = coordinateVector c j p := rfl
  have hb (i j : Fin n) : P202.TorsionMetricData.bracket (E i) (E j) = 0 := by
    apply ConnectionForms.section_ext
    intro p
    exact LeviCivita.coordinate_bracket_zero c p (hc p) i j (E i) (E j)
      (Eventually.of_forall (hE i)) (Eventually.of_forall (hE j))
  have hmetric (i j : Fin n) :
      (fun p => pairing g p ((E i).val p) ((E j).val p)) =
        (fun _ => if i = j then (1 : ℝ) else 0) := by
    funext p
    exact congrFun (congrFun (hg p) i) j
  have hp (i j l : Fin n) (p : M) :
      pairing g p ((C.cov (E i) (E j)).val p) (coordinateVector c l p) = 0 := by
    have hk := LeviCivita.koszul_formula g C hC (E i) (E j) (E l) p
    unfold koszulRHS at hk
    rw [hmetric, hmetric, hmetric, hb, hb, hb,
      scalarDerivative_constant, scalarDerivative_constant, scalarDerivative_constant] at hk
    simp only [ConnectionForms.section_zero_apply, pairing, map_zero, LinearMap.zero_apply,
      add_zero, sub_zero, hE] at hk
    change 2 * pairing g p ((C.cov (E i) (E j)).val p) (coordinateVector c l p) = 0 at hk
    linarith
  have hcov (i j : Fin n) : C.cov (E i) (E j) = 0 := by
    apply ConnectionForms.section_ext
    intro p
    apply ((tangentBundle S).fiberCoordinates c p (hc p)).injective
    ext k
    rw [ConnectionForms.section_zero_apply, map_zero]
    change ((tangentBundle S).fiberCoordinates c p (hc p) ((C.cov (E i) (E j)).val p)) k = 0
    rw [LeviCivita.coordinates_from_metric g c p (hc p) _ k]
    simp only [hp, mul_zero, Finset.sum_const_zero, Pi.zero_apply]
  have hcurv (i j k : Fin n) (p : M) :
      R.val p (coordinateVector c i p) (coordinateVector c j p) (coordinateVector c k p) = 0 := by
    change R.val p ((E i).val p) ((E j).val p) ((E k).val p) = 0
    rw [hR, CurvatureAlgebra.curvature_apply, hcov, hcov, hb]
    have hz : C.cov 0 (E k) = 0 := by
      have he := LinearMap.congr_fun C.cov.map_zero (E k)
      exact he
    rw [hz, (C.cov (E i)).map_zero, (C.cov (E j)).map_zero]
    change (0 : TangentSpace S p) - 0 - 0 = 0
    simp only [LeviCivita.tangent_sub_as_add, smul_zero, add_zero]
  intro p v w z
  rw [← LeviCivita.coordinate_expansion c p (hc p) v,
    ← LeviCivita.coordinate_expansion c p (hc p) w,
    ← LeviCivita.coordinate_expansion c p (hc p) z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    hcurv, smul_zero, Finset.sum_const_zero]
end Cartesian

section Surface
variable {a b : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 a M} {T : SmoothManifold 3 b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)
  {g : RiemannianMetric S} {C : Connection (tangentBundle S)}
  {D : letI := P.space.topology; Connection P.space.bundle}
  (G : Geometry i P hP W g C D)
include W

/-- In codimension one the actual normal space is a line. -/
theorem normal_finrank (p : M) : Module.finrank ℝ (NormalFiber i P hP p) = 1 := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  exact SmoothManifolds.ConstantRankBundles.finrank_fiber W.orthogonal.right.bundle p

/-- A unit normal spans the normal line, and the scalar second form is its
coefficient, independently of any extension of the normal away from p. -/
theorem normal_expansion (p : M) (ν : NormalFiber i P hP p)
    (hν : ambientForm P hP p ν.val ν.val = 1) (z : NormalFiber i P hP p) :
    z.val = ambientForm P hP p z.val ν.val • ν.val := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  have hn : ν ≠ 0 := by
    intro hz
    have : ambientForm P hP p ν.val ν.val = 0 := by simp [hz]
    linarith
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (normal_finrank i P hP W p) hn z
  have hv : c • ν.val = z.val := congrArg Subtype.val hc
  rw [← hv, LinearMap.BilinForm.smul_left, hν, mul_one]

/-- Pairing two normal vectors is multiplication of their scalar components. -/
theorem normal_pairing (p : M) (ν : NormalFiber i P hP p)
    (hν : ambientForm P hP p ν.val ν.val = 1) (z t : NormalFiber i P hP p) :
    ambientForm P hP p z.val t.val = ambientForm P hP p z.val ν.val * ambientForm P hP p t.val ν.val := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  conv_lhs => rw [normal_expansion i P hP W p ν hν z,
    normal_expansion i P hP W p ν hν t]
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hν]
  ring

/-- The matrix identity g A = B in an arbitrary tangent basis. -/
theorem matrix_shape (p : M) (ν : NormalFiber i P hP p)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace S p)) :
    firstFormMatrix g p e * LinearMap.toMatrix e e (shapeOperator i P hP W G p ν) =
      secondFormMatrix i P hP W G p ν e := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  ext j k
  simp only [Matrix.mul_apply, firstFormMatrix, secondFormMatrix, scalarSecondForm,
    LinearMap.toMatrix_apply]
  change (∑ l : Fin 2, pairing g p (e j) (e l) * e.repr (shapeOperator i P hP W G p ν (e k)) l) =
    ambientForm P hP p (secondTensor i P hP W G p (e j) (e k)).val ν.val
  have he := congrArg (fun z => pairing g p (e j) z) (e.sum_repr (shapeOperator i P hP W G p ν (e k)))
  simp only [pairing, map_sum, map_smul, smul_eq_mul] at he
  calc
    _ = ∑ l : Fin 2, e.repr (shapeOperator i P hP W G p ν (e k)) l * pairing g p (e j) (e l) := by
      apply Finset.sum_congr rfl
      intro l _
      exact mul_comm _ _
    _ = pairing g p (e j) (shapeOperator i P hP W G p ν (e k)) := he
    _ = pairing g p (shapeOperator i P hP W G p ν (e j)) (e k) :=
      (G.selfAdjoint p ν (e j) (e k)).symm
    _ = _ := G.adjoint p ν (e j) (e k)

theorem shape_det_ratio (p : M) (ν : NormalFiber i P hP p)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace S p)) :
    LinearMap.det (A := ℝ) (M := TangentSpace S p) (shapeOperator i P hP W G p ν) =
      (secondFormMatrix i P hP W G p ν e).det / (firstFormMatrix g p e).det := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  apply (eq_div_iff (firstForm_det_pos g p e).ne').mpr
  calc
    _ = (firstFormMatrix g p e).det * LinearMap.det (A := ℝ) (M := TangentSpace S p)
        (shapeOperator i P hP W G p ν) := mul_comm _ _
    _ = (firstFormMatrix g p e).det *
        (LinearMap.toMatrix e e (shapeOperator i P hP W G p ν)).det :=
      congrArg (fun r : ℝ => (firstFormMatrix g p e).det * r)
        (LinearMap.det_toMatrix (A := ℝ) (M := TangentSpace S p) (ι := Fin 2) e (shapeOperator i P hP W G p ν)).symm
    _ = (firstFormMatrix g p e * LinearMap.toMatrix e e (shapeOperator i P hP W G p ν)).det :=
      (Matrix.det_mul _ _).symm
    _ = _ := congrArg Matrix.det (matrix_shape i P hP W G p ν e)

theorem second_det_normal_reversal (p : M) (ν : NormalFiber i P hP p)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace S p)) :
    (secondFormMatrix i P hP W G p ((-1 : ℝ) • ν) e).det =
      (secondFormMatrix i P hP W G p ν e).det := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  simp only [secondFormMatrix, scalarSecondForm, Submodule.coe_smul,
    LinearMap.BilinForm.smul_right, Matrix.det_fin_two]
  ring

theorem shape_det_normal_reversal (p : M) (ν : NormalFiber i P hP p)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace S p)) :
    LinearMap.det (A := ℝ) (M := TangentSpace S p) (shapeOperator i P hP W G p ((-1 : ℝ) • ν)) = LinearMap.det (A := ℝ) (M := TangentSpace S p) (shapeOperator i P hP W G p ν) := by
  calc
    _ = (secondFormMatrix i P hP W G p ((-1 : ℝ) • ν) e).det / (firstFormMatrix g p e).det :=
      shape_det_ratio i P hP W G p ((-1 : ℝ) • ν) e
    _ = (secondFormMatrix i P hP W G p ν e).det / (firstFormMatrix g p e).det :=
      congrArg (fun r : ℝ => r / (firstFormMatrix g p e).det)
        (second_det_normal_reversal i P hP W G p ν e)
    _ = _ := (shape_det_ratio i P hP W G p ν e).symm

/-- Gauss's equation on arbitrary fiber vectors, rather than only on fields. -/
theorem gauss_fiber (R₀ : CurvatureTensor S) (R : CurvatureTensor T)
    (hE : AmbientEquations G R₀ R) (p : M) (v w z t : TangentSpace S p) :
    curvatureForm g R₀ p v w z t =
      ambientForm P hP p (R.val (F p) (i.differential p v) (i.differential p w)
        (i.differential p z)) (i.differential p t) +
      ambientForm P hP p (secondTensor i P hP W G p v t).val (secondTensor i P hP W G p w z).val -
      ambientForm P hP p (secondTensor i P hP W G p w t).val (secondTensor i P hP W G p v z).val := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  let X := CurvatureAlgebra.fieldLift p v
  let Y := CurvatureAlgebra.fieldLift p w
  let Z := CurvatureAlgebra.fieldLift p z
  let V := CurvatureAlgebra.fieldLift p t
  simpa only [X, Y, Z, V, CurvatureAlgebra.fieldLift_value] using hE.1 X Y Z V p

/-- The determinant quotient from the flat Gauss equation, with no choice of
orthonormal coordinates. -/
theorem sectional_ratio (R₀ : CurvatureTensor S) (R : CurvatureTensor T)
    (hE : AmbientEquations G R₀ R) (hflat : ∀ p v w z, R.val (F p) v w z = 0)
    (p : M) (ν : NormalFiber i P hP p) (hν : ambientForm P hP p ν.val ν.val = 1)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace S p))
    (he : LinearIndependent ℝ ![e 0, e 1]) :
    sectionalCurvature g R₀ p (e 0) (e 1) he =
      (secondFormMatrix i P hP W G p ν e).det / (firstFormMatrix g p e).det := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  have hg := gauss_fiber i P hP W G R₀ R hE p (e 0) (e 1) (e 1) (e 0)
  rw [hflat] at hg
  simp only [map_zero, LinearMap.zero_apply, zero_add] at hg
  rw [normal_pairing i P hP W p ν hν (secondTensor i P hP W G p (e 0) (e 0))
    (secondTensor i P hP W G p (e 1) (e 1)),
    normal_pairing i P hP W p ν hν (secondTensor i P hP W G p (e 1) (e 0))
    (secondTensor i P hP W G p (e 0) (e 1))] at hg
  unfold sectionalCurvature
  rw [hg]
  simp only [secondFormMatrix, scalarSecondForm, firstFormMatrix, Matrix.det_fin_two]
  have hsym : pairing g p (e 1) (e 0) = pairing g p (e 0) (e 1) := g.symmetric p _ _
  rw [G.symmetric p (e 1) (e 0), hsym]
  simp only [pow_two]

end Surface

theorem flat_surface_formula : P202Specs.Geometry.TheoremaEgregium.flat_surface_formulaType.{u} := by
  intro a b M N _ _ S T F i P
  letI := P.space.topology
  intro hP W g C K D hC hK hi hD R₀ R hR₀ hR hflat G p ν hν e he
  have hE := GaussCodazziRicci.ambient_equations i P hP W g C K D hC hK hi hD
    R₀ R hR₀ hR G
  have hratio := sectional_ratio i P hP W G R₀ R hE hflat p ν hν e he
  exact ⟨firstForm_det_pos g p e,
    hratio.trans (shape_det_ratio i P hP W G p ν e).symm, hratio,
    shape_det_normal_reversal i P hP W G p ν e,
    second_det_normal_reversal i P hP W G p ν e⟩


/-- Corollary 7.6 for Euclidean three-space with its standard metric.
Ambient flatness is proved from Cartesian metric coefficients. -/
theorem euclidean_surface_formula :
    P202Specs.Geometry.TheoremaEgregium.euclidean_surface_formulaType := by
  intro a M _ S T g h hstd F i hi C K hC hK R₀ R hR₀ hR P
  letI := P.space.topology
  obtain ⟨c, hsource, _hidentity, hg⟩ := hstd
  have hc : ∀ q, q ∈ (tangentBundle T).baseSet c := by
    intro q
    rw [(tangentRealization T).baseSet, hsource]
    exact Set.mem_univ q
  have hflat := cartesian_curvature_zero h K hK R hR c hc hg
  obtain ⟨hP, D, W, hhP, hD, ⟨G⟩⟩ :=
    GaussCodazziRicci.geometry_exists g h F i hi C K hC hK P
  have hiP : ∀ p v w,
      hP.form p (i.differential p v) (i.differential p w) = pairing g p v w := by
    intro p v w
    rw [hhP]
    exact hi p v w
  exact ⟨hP, D, W, G, hhP, hD,
    flat_surface_formula i P hP W g C K D hC hK.1 hiP hD R₀ R hR₀ hR
      (fun p => hflat (F p)) G⟩

section Naturality
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  (g : RiemannianMetric S) (h : RiemannianMetric T)
  (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
  (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
  (R₀ : CurvatureTensor S) (R : CurvatureTensor T)
  (hR₀ : RepresentsCurvature C R₀) (hR : RepresentsCurvature K R)
  (f : M → N) (hi : IsLocalIsometry g h f) (hf : IsSmoothMap S T f)
include g h C K hC hK hR₀ hR hi

/-- Parallelism of df implies naturality of the curvature tensor. The use of
pullback sections avoids any assumption of global projectability of fields. -/
theorem localIsometry_tensor (p : M) (v w z : TangentSpace S p) :
    R.val (f p) (SmoothManifolds.differential S T f hf p v)
      (SmoothManifolds.differential S T f hf p w)
      (SmoothManifolds.differential S T f hf p z) =
    SmoothManifolds.differential S T f hf p (R₀.val p v w z) := by
  let P := P202.PullbackData.bundle (tangentBundle T) S f hf
  letI := P.space.topology
  obtain ⟨D, hD, _⟩ := PullbackConnections.exists_unique (tangentBundle T) f hf P K
  let lift := LeviCivita.differentialSection f hf P
  have hl (Y : Field S) (q : M) :
      (lift Y).val q = SmoothManifolds.differential S T f hf q (Y.val q) := rfl
  have hc (X Y : Field S) : D.cov X (lift Y) = lift (C.cov X Y) := by
    obtain ⟨t, ht, hcov⟩ := LeviCivita.localIsometry_intertwines g h C K hC hK f hi hf P D hD Y
    have he : t = lift Y := ConnectionForms.section_ext (fun q => ht q)
    apply ConnectionForms.section_ext
    intro q
    rw [← he]
    exact hcov X q
  let X := CurvatureAlgebra.fieldLift p v
  let Y := CurvatureAlgebra.fieldLift p w
  let Z := CurvatureAlgebra.fieldLift p z
  have he := GaussCodazziRicci.curvature_pullback f hf P K D hD hK.1 R hR X Y (lift Z) p
  rw [GaussCodazziRicci.bundleCurvature_apply, hc, hc, hc, hc, hc] at he
  simp only [hl] at he
  have he' : SmoothManifolds.differential S T f hf p
      ((C.cov X (C.cov Y Z)).val p - (C.cov Y (C.cov X Z)).val p -
        (C.cov (P202.TorsionMetricData.bracket X Y) Z).val p) =
      R.val (f p) (SmoothManifolds.differential S T f hf p (X.val p))
        (SmoothManifolds.differential S T f hf p (Y.val p))
        (SmoothManifolds.differential S T f hf p (Z.val p)) := by
    simpa only [LeviCivita.tangent_sub_as_add, map_add, map_smul] using he
  have hrep : (C.cov X (C.cov Y Z)).val p - (C.cov Y (C.cov X Z)).val p -
      (C.cov (P202.TorsionMetricData.bracket X Y) Z).val p =
      R₀.val p (X.val p) (Y.val p) (Z.val p) := by
    rw [hR₀, CurvatureAlgebra.curvature_apply]
  rw [hrep] at he'
  simpa only [hl, X, Y, Z, CurvatureAlgebra.fieldLift_value] using he'.symm

end Naturality

theorem localIsometry_curvature : P202Specs.Geometry.TheoremaEgregium.localIsometry_curvatureType.{u} := by
  intro n m a b M N _ _ S T g h C K hC hK R₀ R hR₀ hR f hi hf p v w hv
  let L := SmoothManifolds.differential S T f hf
  obtain ⟨i, _⟩ := SmoothMetrics.localIsometry_isIsometricImmersion g h f hi
  have hIL : i.differential p = L p :=
    (SmoothManifolds.differential_exists S T f hf p).unique (i.isDifferential p)
      (SmoothManifolds.differential_spec S T f hf p)
  have hinj : Function.Injective (L p) := hIL ▸ i.injective p
  have hwi : LinearIndependent ℝ ((L p) ∘ ![v, w]) := hv.map_injOn (L p) hinj.injOn
  have hw : LinearIndependent ℝ ![L p v, L p w] := by
    convert hwi using 1
    ext j
    fin_cases j <;> rfl
  refine ⟨hw, ?_⟩
  have hn := localIsometry_tensor g h C K hC hK R₀ R hR₀ hR f hi hf p v w w
  obtain ⟨_, A, hA, hmA⟩ := hi
  have hAL : A = L := by
    funext q
    exact (SmoothManifolds.differential_exists S T f hf q).unique
      (hA q) (SmoothManifolds.differential_spec S T f hf q)
  have hm : IsMetricPreserving g h f L := hAL ▸ hmA
  unfold sectionalCurvature curvatureForm
  rw [hn, hm p, hm p, hm p, hm p]

end P202.Geometry.TheoremaEgregium
