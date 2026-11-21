import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConstantCurvaturePolar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SectionalRecovery
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialJacobi
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.Geometry.ConstantCurvaturePolar
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.ConnectionData P202.MetricData
  P202.CurveConnectionData P202.LeviCivitaData P202.GeodesicData P202.CurvatureData
  P202.JacobiData P202.ExponentialData P202.ExponentialJacobiData
  P202.ConstantCurvaturePolarData
open Set Filter
open scoped Topology
universe u

lemma s_zero (k : ℝ) : s k 0 = 0 := by
  simp [s]

lemma c_zero (k : ℝ) : c k 0 = 1 := by
  simp [c]

lemma s_derivative (k t : ℝ) : HasDerivAt (s k) (c k t) t := by
  unfold s c
  by_cases hk : 0 < k
  · have hne := ne_of_gt (Real.sqrt_pos.mpr hk)
    simpa [s, c, hk, hne] using!
      (((hasDerivAt_id t).const_mul (Real.sqrt k)).sin.div_const (Real.sqrt k))
  · by_cases hz : k = 0
    · subst k
      simpa [s, c] using! hasDerivAt_id t
    · have hneg : 0 < -k := by
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hk) hz)
      have hne := ne_of_gt (Real.sqrt_pos.mpr hneg)
      simpa [s, c, hk, hz, hne] using!
        (((hasDerivAt_id t).const_mul (Real.sqrt (-k))).sinh.div_const (Real.sqrt (-k)))

lemma c_derivative (k t : ℝ) : HasDerivAt (c k) (-k * s k t) t := by
  unfold s c
  by_cases hk : 0 < k
  · have hne := ne_of_gt (Real.sqrt_pos.mpr hk)
    have hs := Real.sq_sqrt hk.le
    have heq : -Real.sin (Real.sqrt k * t) * Real.sqrt k =
        -k * (Real.sin (Real.sqrt k * t) / Real.sqrt k) := by
      field_simp
      rw [hs]
      ring
    simpa only [ite_eq_left hk, id_eq, mul_one, heq] using!
      (((hasDerivAt_id t).const_mul (Real.sqrt k)).cos)
  · by_cases hz : k = 0
    · subst k
      simpa [s, c] using hasDerivAt_const t (1 : ℝ)
    · have hneg : 0 < -k := by
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hk) hz)
      have hne := ne_of_gt (Real.sqrt_pos.mpr hneg)
      have hs := Real.sq_sqrt hneg.le
      have heq : Real.sinh (Real.sqrt (-k) * t) * Real.sqrt (-k) =
          -k * (Real.sinh (Real.sqrt (-k) * t) / Real.sqrt (-k)) := by
        field_simp
        rw [hs]
        ring
      simpa only [ite_eq_right hk, ite_eq_right hz, id_eq, mul_one, heq] using!
        (((hasDerivAt_id t).const_mul (Real.sqrt (-k))).cosh)

lemma scalar_model_proof : P202Specs.Geometry.ConstantCurvaturePolar.scalar_modelType := by
  intro k
  have hd : deriv (s k) = c k := funext fun t => (s_derivative k t).deriv
  refine ⟨s_zero k, c_zero k, s_derivative k, c_derivative k, ?_, ?_⟩
  · intro t
    rw [hd, (c_derivative k t).deriv]
    ring
  · rw [hd, c_zero]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

lemma parallel_properties (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (w : TangentSpace S (q 0).1) :
    parallel C I q w 0 = w ∧ ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun t => (q t).1) (parallel C I q w) t 0 := by
  classical
  obtain ⟨P, hP0, hP, _⟩ := JacobiIVP.global_parallel_ivp C I q hq 0 h0 w
  have hex : ∃ P : (t : ℝ) → TangentSpace S (q t).1,
      P 0 = w ∧ ∀ t ∈ I.carrier,
        HasCovariantDerivativeAt C (fun t => (q t).1) P t 0 := ⟨P, hP0, hP⟩
  simpa only [parallel, dite_eq_left hex] using Classical.choose_spec hex

lemma parallel_eq_global (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (w : TangentSpace S (q 0).1) (t : ℝ) (ht : t ∈ I.carrier) :
    parallel C I q w t = JacobiIVP.globalParallelField C I q hq 0 h0 w t := by
  have hP := parallel_properties C I q hq h0 w
  exact JacobiIVP.globalParallelField_unique C I q hq 0 h0 w
    (parallel C I q w) hP.1 hP.2 t ht

lemma pairing_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (f h : (t : ℝ) → TangentSpace S (q t).1)
    (hf : ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun t => (q t).1) f t 0)
    (hh : ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun t => (q t).1) h t 0)
    (h0 : 0 ∈ I.carrier) (t : ℝ) (ht : t ∈ I.carrier) :
    pairing g (q t).1 (f t) (h t) = pairing g (q 0).1 (f 0) (h 0) := by
  obtain ⟨a, ha⟩ := I.isOpen.exists_is_const_of_deriv_eq_zero
    I.ordConnected.isPreconnected
    (fun t ht => by
      have hd := ParallelTransport.metric_pairing_deriv C g hC.2
        (mem_univ t) uniqueDiffWithinAt_univ (hf t ht) (hh t ht)
      rw [hasDerivWithinAt_univ] at hd
      exact hd.differentiableAt.differentiableWithinAt)
    (fun t ht => by
      have hd := ParallelTransport.metric_pairing_deriv C g hC.2
        (mem_univ t) uniqueDiffWithinAt_univ (hf t ht) (hh t ht)
      have hz : HasDerivAt (fun t => pairing g (q t).1 (f t) (h t)) 0 t := by
        simpa only [hasDerivWithinAt_univ, pairing, map_zero,
          LinearMap.zero_apply, add_zero] using hd
      exact hz.deriv)
  exact (ha t ht).trans (ha 0 h0).symm

lemma radial_curvature (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (k : ℝ) (hk : ConstantSectional g R k) (p : M)
    (v w : TangentSpace S p) (hv : pairing g p v v = 1)
    (hw : pairing g p w v = 0) : R.val p w v v = k • w := by
  have heq : ∀ z : TangentSpace S p,
      pairing g p (R.val p w v v - k • w) z = 0 := by
    intro z
    have h := SectionalRecovery.curvature_constant g C hC R hR p k (hk p) w v v z
    change pairing g p (R.val p w v v) z = _ at h
    rw [hv, hw] at h
    rw [LinearMap.BilinForm.sub_left (B₁ := pairing g p) (R.val p w v v) (k • w) z,
      LinearMap.BilinForm.smul_left (B := pairing g p) k w z, h]
    ring
  by_contra hn
  have hne : R.val p w v v - k • w ≠ 0 := sub_ne_zero.mpr hn
  have hp := g.positive p _ hne
  have hz := heq (R.val p w v v - k • w)
  change 0 < pairing g p _ _ at hp
  linarith

lemma normal_jacobi_proof : P202Specs.Geometry.ConstantCurvaturePolar.normal_jacobiType.{u} := by
  intro n M _ S g C hC R hR k hk I q hq h0 hunit w hw
  let P := parallel C I q w
  have hP : P 0 = w ∧ ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun t => (q t).1) P t 0 :=
    parallel_properties C I q hq h0 w
  have hnormal (t : ℝ) (ht : t ∈ I.carrier) :
      pairing g (q t).1 (P t) (q t).2 = 0 := by
    rw [pairing_constant g C hC I q P (fun t => (q t).2) hP.2
      (fun t ht => (hq t ht).2) h0 t ht, hP.1]
    exact hw
  have hJ : IsJacobiField C R I.carrier q (fun t => s k t • P t) := by
    refine ⟨fun t => c k t • P t, ?_⟩
    intro t ht
    constructor
    · simpa only [smul_zero, add_zero] using CurveCovariantDerivative.derivative_smul C
        (hP.2 t ht) (s_derivative k t).hasDerivWithinAt
    · have hd := CurveCovariantDerivative.derivative_smul C
        (hP.2 t ht) (c_derivative k t).hasDerivWithinAt
      have hr := radial_curvature g C hC R hR k hk (q t).1 (q t).2 (P t)
        (hunit t ht) (hnormal t ht)
      simpa only [smul_zero, add_zero, map_smul, LinearMap.smul_apply,
        hr, smul_smul, neg_mul, neg_smul, mul_comm, mul_left_comm] using hd
  have hJ0 : s k 0 • P 0 = 0 := by rw [s_zero, zero_smul]
  have hD0 : HasCovariantDerivativeAt C (fun t => (q t).1)
      (fun t => s k t • P t) 0 w := by
    have hd := CurveCovariantDerivative.derivative_smul C
      (hP.2 0 h0) (s_derivative k 0).hasDerivWithinAt
    simpa only [c_zero, one_smul, s_zero, zero_smul, add_zero, hP.1] using hd
  refine ⟨hJ, hJ0, hD0, ?_, ?_⟩
  · intro t ht
    change pairing g (q t).1 (s k t • P t) (q t).2 = 0
    rw [LinearMap.BilinForm.smul_left, hnormal t ht, mul_zero]
  · intro K hK hK0 hKD t ht
    obtain ⟨L, _, _, _, huniq⟩ := JacobiIVP.exists_unique S g C hC R hR I q hq 0 h0 0 w
    exact (huniq K hK hK0 hKD t ht).trans
      (huniq (fun t => s k t • P t) hJ hJ0 hD0 t ht).symm

/-- Pairings commute with the equality identification of tangent fibers. -/
lemma pairing_cast {p q : M} (g : RiemannianMetric S) (h : p = q)
    (w z : TangentSpace S p) :
    pairing g q (castTangent S h w) (castTangent S h z) = pairing g p w z := by
  subst q
  rfl

lemma pairing_heq {p q : M} (g : RiemannianMetric S) (h : p = q)
    {w z : TangentSpace S p} {w' z' : TangentSpace S q}
    (hw : HEq w w') (hz : HEq z z') : pairing g p w z = pairing g q w' z' := by
  subst q
  cases hw
  cases hz
  rfl

lemma initial_velocity (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v : TangentSpace S p) :
    initialIdentification S C F hF p v v = (F.curve ⟨p, v⟩ 0).2 := by
  have aux (z : Phase S) (h : z = ⟨p, v⟩) :
      castTangent S (congrArg Sigma.fst h).symm v = z.2 := by
    cases h
    rfl
  exact aux _ (hF ⟨p, v⟩).2.1

/-- Recover the actual radial time from membership in the exponential domain;
negative times are included. -/
lemma time_mem_of_domain (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v : TangentSpace S p)
    (t : ℝ) (ht : t ≠ 0) (hdom : (⟨p, t • v⟩ : Phase S) ∈ exponentialDomain F) :
    t ∈ (F.interval ⟨p, v⟩).carrier := by
  obtain ⟨J, hJ, hmax⟩ := GeodesicIVP.maximal_affine S C ⟨p, v⟩
    (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩) (hF ⟨p, v⟩) t 0 ht (hF ⟨p, v⟩).1
  have hi : affineCurve S (F.curve ⟨p, v⟩) t 0 0 = (⟨p, t • v⟩ : Phase S) := by
    change (⟨(F.curve ⟨p, v⟩ (t * 0 + 0)).1,
      t • (F.curve ⟨p, v⟩ (t * 0 + 0)).2⟩ : Phase S) = _
    rw [mul_zero, add_zero, (hF ⟨p, v⟩).2.1]
  rw [hi] at hmax
  obtain ⟨hI, _⟩ := GeodesicIVP.maximal_unique S C ⟨p, t • v⟩
    (F.interval ⟨p, t • v⟩) J (F.curve ⟨p, t • v⟩)
    (affineCurve S (F.curve ⟨p, v⟩) t 0) (hF ⟨p, t • v⟩) hmax
  change 1 ∈ (F.interval ⟨p, t • v⟩).carrier at hdom
  rw [hI, hJ] at hdom
  simpa only [affineDomain, mem_ofPred_eq, mul_one, add_zero] using hdom

lemma gauss_selected (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (x y : TangentSpace S p)
    (hx : (⟨p, x⟩ : Phase S) ∈ exponentialDomain F) :
    pairing g (fiberExponential F p x) (fiberDifferential S F p x x)
      (fiberDifferential S F p x y) = pairing g p x y := by
  exact GaussLemma.gauss_lemma S g C hC F hF p x hx
    (selectedChart S p).val (selectedChart S p).property.1 (selectedChart S p).property.2
    (selectedChart S (fiberExponential F p x)).val
    (selectedChart S (fiberExponential F p x)).property.1
    (selectedChart S (fiberExponential F p x)).property.2 y

lemma angular_pairing
    (hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (k : ℝ) (hk : ConstantSectional g R k)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (t : ℝ) (v : TangentSpace S p)
    (ht : t ∈ (F.interval ⟨p, v⟩).carrier) (hv : pairing g p v v = 1)
    (w z : TangentSpace S p) (hw : pairing g p w v = 0) (hz : pairing g p z v = 0) :
    pairing g (fiberExponential F p (t • v))
      (fiberDifferential S F p (t • v) (t • w))
      (fiberDifferential S F p (t • v) (t • z)) = s k t ^ 2 * pairing g p w z := by
  let I := F.interval ⟨p, v⟩
  let q := F.curve ⟨p, v⟩
  let E := initialIdentification S C F hF p v
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v⟩).2.2.1
  have h0 : 0 ∈ I.carrier := (hF ⟨p, v⟩).1
  have hE (x y : TangentSpace S p) :
      pairing g (q 0).1 (E x) (E y) = pairing g p x y :=
    pairing_cast g _ x y
  have hunit (r : ℝ) (hr : r ∈ I.carrier) :
      pairing g (q r).1 (q r).2 (q r).2 = 1 := by
    rw [← JacobiIVP.speed_sq_constant g C hC I q hq h0 hr,
      ← initial_velocity C F hF p v]
    exact (hE v v).trans hv
  have horth (x : TangentSpace S p) (hx : pairing g p x v = 0) :
      pairing g (q 0).1 (E x) (q 0).2 = 0 := by
    rw [← initial_velocity C F hF p v]
    exact (hE x v).trans hx
  let Pw := parallel C I q (E w)
  let Pz := parallel C I q (E z)
  have hJw := normal_jacobi_proof S g C hC R hR k hk I q hq h0 hunit (E w) (horth w hw)
  have hJz := normal_jacobi_proof S g C hC R hR k hk I q hq h0 hunit (E z) (horth z hz)
  have hew := hformula S g C hC R hR F hF p v w
    (fun r => s k r • Pw r) hJw.1 hJw.2.1 hJw.2.2.1 t ht
  have hez := hformula S g C hC R hR F hF p v z
    (fun r => s k r • Pz r) hJz.1 hJz.2.1 hJz.2.2.1 t ht
  have hp := (ExponentialNormalCoordinates.radial_identity S C F hF p v t ht).2
  rw [← pairing_heq g hp.symm hew hez]
  simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  have hPw := parallel_properties C I q hq h0 (E w)
  have hPz := parallel_properties C I q hq h0 (E z)
  have hPw0 : Pw 0 = E w := hPw.1
  have hPz0 : Pz 0 = E z := hPz.1
  rw [pairing_constant g C hC I q Pw Pz hPw.2 hPz.2 h0 t ht, hPw0, hPz0, hE]
  ring

lemma polar_metric_proof
    (hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u}) :
    P202Specs.Geometry.ConstantCurvaturePolar.polar_metricType.{u} := by
  intro n M _ S g C hC R hR k hk F hF p t v ht hv hdom a b w z hw hz
  let L := fiberDifferential S F p (t • v)
  let B := pairing g (fiberExponential F p (t • v))
  have htmem := time_mem_of_domain C F hF p v t ht hdom
  have hrad : B (L v) (L v) = 1 := by
    have he := gauss_selected g C hC F hF p (t • v) v hdom
    have hh : t * B (L v) (L v) = t * 1 := by
      simpa only [map_smul, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, LinearMap.BilinForm.smul_left, hv, mul_one] using he
    exact (mul_left_cancel₀ ht hh)
  have hcross (x : TangentSpace S p) (hx : pairing g p x v = 0) :
      B (L v) (L (t • x)) = 0 := by
    have he := gauss_selected g C hC F hF p (t • v) (t • x) hdom
    have hvx : pairing g p v x = 0 := by exact (g.symmetric p v x).trans hx
    have hh : t * B (L v) (L (t • x)) = 0 := by
      simpa only [map_smul, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right, hvx, mul_zero] using he
    exact (mul_eq_zero.mp hh).resolve_left ht
  have hang := angular_pairing hformula g C hC R hR k hk F hF p t v htmem hv w z hw hz
  change B (L (a • v + t • w)) (L (b • v + t • z)) = _
  simp only [map_add, map_smul, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  have hw' : B (L w) (L v) = 0 := by
    have hh := hcross w hw
    have hh' : t * B (L v) (L w) = 0 := by
      simpa only [map_smul, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, LinearMap.BilinForm.smul_right, mul_comm] using hh
    exact (g.symmetric _ (L w) (L v)).trans ((mul_eq_zero.mp hh').resolve_left ht)
  have hz' : B (L v) (L z) = 0 := by
    have hh := hcross z hz
    have hh' : t * B (L v) (L z) = 0 := by
      simpa only [map_smul, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, LinearMap.BilinForm.smul_right, mul_comm] using hh
    exact (mul_eq_zero.mp hh').resolve_left ht
  change B (L (t • w)) (L (t • z)) = _ at hang
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hang
  rw [hrad, hw', hz']
  nlinarith [hang]

lemma polar_derivative_proof
    (hcoordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u}) :
    P202Specs.Geometry.ConstantCurvaturePolar.polar_derivativeType.{u} := by
  intro n M _ S C F hF p t v hdom d hd hq a w
  let e := (selectedChart S p).val
  have he : e ∈ S.smoothStructure.val := (selectedChart S p).property.1
  have hp : p ∈ e.source := (selectedChart S p).property.2
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let f := fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val
  have hf := GaussLemma.fiberDifferential_hasFDerivAt C F hF p (t • v) hdom e he hp d hd hq
  have hr : HasDerivAt (fun r : ℝ => t + r * a) a 0 := by
    simpa only [id_eq, one_mul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) t).fun_add ((hasDerivAt_id (0 : ℝ)).mul_const a)
  have hvw : HasDerivAt (fun r : ℝ => E v + r • E w) (E w) 0 := by
    simpa only [id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) (E v)).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const (E w))
  have hline : HasDerivAt (fun r : ℝ => (t + r * a) • (E v + r • E w))
      (a • E v + t • E w) 0 := by
    simpa only [zero_mul, add_zero, zero_add, zero_smul, add_comm] using hr.fun_smul hvw
  have hchain := hf.comp_hasDerivAt_of_eq 0 hline (by
    change E (t • v) = (t + 0 * a) • (E v + 0 • E w)
    simp only [zero_mul, add_zero, zero_smul, map_smul])
  have heq := hcoordinates S C F hF p (t • v) hdom e d he hd hp hq (a • v + t • w)
  change HasDerivAt _ ((tangentStructure S).fiberCoordinates.equiv d hd _ hq
    (fiberDifferential S F p (t • v) (a • v + t • w))) 0
  rw [heq]
  simpa only [E, Function.comp_def, map_smul, map_add,
    LinearEquiv.symm_apply_apply] using hchain

lemma normal_ball_metric_proof
    (hformula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u}) :
    P202Specs.Geometry.ConstantCurvaturePolar.normal_ball_metricType.{u} := by
  intro n M _ S g C hC R hR k hk F hF p E _ r d hc t v ht htr hv
  have hn : tangentNorm g p v = 1 := by simp [tangentNorm, hv]
  have htn : tangentNorm g p (t • v) < r := by
    rw [SmoothMetrics.tangentNorm_smul, hn, abs_of_pos ht, mul_one]
    exact htr
  let x : ModelSpace n .euclidean := ⟨E (t • v), by simp [modelSet]⟩
  have hx : tangentNorm g p (E.symm x.val) < r := by
    simpa only [x, LinearEquiv.symm_apply_apply] using htn
  have hex := hc.2.2.2.2.2 x hx
  have hdom : (⟨p, t • v⟩ : Phase S) ∈ exponentialDomain F := by
    simpa only [x, LinearEquiv.symm_apply_apply] using hex.1
  refine ⟨?_, ?_⟩
  · simpa only [x, LinearEquiv.symm_apply_apply] using hex.2
  · exact polar_metric_proof hformula S g C hC R hR k hk F hF p t v (ne_of_gt ht) hv hdom

lemma angular_zero_proof : P202Specs.Geometry.ConstantCurvaturePolar.angular_zeroType.{u} := by
  intro M _ S g p v w hv hw
  have hvne : v ≠ 0 := by
    intro hh
    rw [hh] at hv
    simp [pairing] at hv
  have hnot : ¬ LinearIndependent ℝ ![w, v] := by
    intro h
    let _ := (SmoothManifolds.tangent_dimension S p).1
    have hh := h.fintype_card_le_finrank
    rw [(SmoothManifolds.tangent_dimension S p).2] at hh
    have htwo : 2 ≤ 1 := by simpa using hh
    omega
  by_contra hwne
  apply hnot
  apply (linearIndependent_fin2 (K := ℝ) (f := ![w, v])).mpr
  change v ≠ 0 ∧ ∀ a : ℝ, a • v ≠ w
  refine ⟨hvne, ?_⟩
  intro a ha
  have hh := congrArg (fun x => pairing g p x v) ha
  simp only [LinearMap.BilinForm.smul_left, hv, mul_one, hw] at hh
  exact hwne (ha.symm.trans (by rw [hh, zero_smul]))

/-- The scalar model and its initial values, for every real curvature. -/
theorem scalar_model : P202Specs.Geometry.ConstantCurvaturePolar.scalar_modelType :=
  scalar_model_proof

/-- The unique normal Jacobi field on the original geodesic interval. -/
theorem normal_jacobi : P202Specs.Geometry.ConstantCurvaturePolar.normal_jacobiType.{u} :=
  normal_jacobi_proof

/-- The chain rule identifies the polar differential in every atlas chart. -/
theorem polar_derivative : P202Specs.Geometry.ConstantCurvaturePolar.polar_derivativeType.{u} :=
  polar_derivative_proof ExponentialJacobi.differential_coordinates

/-- The full pullback tensor, including degenerate angular directions. -/
theorem polar_metric : P202Specs.Geometry.ConstantCurvaturePolar.polar_metricType.{u} :=
  polar_metric_proof ExponentialJacobi.differential_formula

/-- Specialization to every normal ball. -/
theorem normal_ball_metric : P202Specs.Geometry.ConstantCurvaturePolar.normal_ball_metricType.{u} :=
  normal_ball_metric_proof ExponentialJacobi.differential_formula

/-- In dimension one the angular tangent space is zero. -/
theorem angular_zero : P202Specs.Geometry.ConstantCurvaturePolar.angular_zeroType.{u} :=
  angular_zero_proof

end P202.Geometry.ConstantCurvaturePolar
