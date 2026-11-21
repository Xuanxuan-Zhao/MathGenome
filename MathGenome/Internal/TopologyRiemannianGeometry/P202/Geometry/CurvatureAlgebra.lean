import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 400000
namespace P202.Geometry.CurvatureAlgebra
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.TorsionMetricData
  P202.LeviCivitaData P202.CurvatureData
open Set Filter
open scoped Topology
open ConnectionForms (section_ext section_add_apply section_smul_apply section_zero_apply
  mulSection_apply scalarDerivative_global section_evaluation_surjective)
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable abbrev curvature := @P202.CurvatureData.curvature
noncomputable abbrev curvatureForm := @P202.CurvatureData.curvatureForm
noncomputable abbrev sectionalCurvature := @P202.CurvatureData.sectionalCurvature

variable (C : Connection (tangentBundle S))

@[simp] theorem curvature_apply (X Y Z : Field S) (p : M) :
    (curvature C X Y Z).val p =
      (C.cov X (C.cov Y Z)).val p - (C.cov Y (C.cov X Z)).val p -
        (C.cov (bracket X Y) Z).val p := by
  simp only [curvature, P202.CurvatureData.curvature, section_add_apply,
    section_smul_apply, neg_one_smul]
  abel

@[simp] theorem curvature_skew (X Y Z : Field S) :
    curvature C X Y Z = (-1 : ℝ) • curvature C Y X Z := by
  apply section_ext
  intro p
  simp only [curvature_apply, section_smul_apply]
  rw [TorsionAndMetric.bracket_skew X Y, map_smul, LinearMap.smul_apply,
    section_smul_apply]
  module

@[simp] theorem curvature_add_first (X U Y Z : Field S) :
    curvature C (X + U) Y Z = curvature C X Y Z + curvature C U Y Z := by
  apply section_ext; intro p
  simp only [curvature_apply, TorsionAndMetric.bracket_add_left, map_add,
    LinearMap.add_apply, section_add_apply]
  abel

@[simp] theorem curvature_add_second (X Y U Z : Field S) :
    curvature C X (Y + U) Z = curvature C X Y Z + curvature C X U Z := by
  apply section_ext; intro p
  simp only [curvature_apply, TorsionAndMetric.bracket_add_right, map_add,
    LinearMap.add_apply, section_add_apply]
  abel

@[simp] theorem curvature_add_third (X Y Z U : Field S) :
    curvature C X Y (Z + U) = curvature C X Y Z + curvature C X Y U := by
  apply section_ext; intro p
  simp only [curvature_apply, map_add, section_add_apply]
  abel

@[simp] theorem curvature_smul_first (c : ℝ) (X Y Z : Field S) :
    curvature C (c • X) Y Z = c • curvature C X Y Z := by
  apply section_ext; intro p
  simp only [curvature_apply, TorsionAndMetric.bracket_smul_left, map_smul,
    LinearMap.smul_apply, section_smul_apply]
  module

@[simp] theorem curvature_smul_second (c : ℝ) (X Y Z : Field S) :
    curvature C X (c • Y) Z = c • curvature C X Y Z := by
  apply section_ext; intro p
  simp only [curvature_apply, TorsionAndMetric.bracket_smul_right, map_smul,
    LinearMap.smul_apply, section_smul_apply]
  module

@[simp] theorem curvature_smul_third (c : ℝ) (X Y Z : Field S) :
    curvature C X Y (c • Z) = c • curvature C X Y Z := by
  apply section_ext; intro p
  simp only [curvature_apply, map_smul, section_smul_apply]
  module

theorem curvature_mul_second (f : GlobalSmooth S) (X Y Z : Field S) :
    curvature C X (mulSection f Y) Z = mulSection f (curvature C X Y Z) := by
  apply section_ext; intro p
  simp only [curvature_apply, TorsionAndMetric.bracket_mul_right, C.linear_field,
    C.leibniz, map_add, LinearMap.add_apply, section_add_apply, mulSection_apply]
  module

theorem curvature_mul_first (f : GlobalSmooth S) (X Y Z : Field S) :
    curvature C (mulSection f X) Y Z = mulSection f (curvature C X Y Z) := by
  rw [curvature_skew C (mulSection f X) Y Z, curvature_mul_second]
  apply section_ext; intro p
  rw [section_smul_apply, mulSection_apply, mulSection_apply, curvature_skew C X Y Z,
    section_smul_apply]
  exact smul_comm _ _ _

theorem curvature_mul_third (f : GlobalSmooth S) (X Y Z : Field S) :
    curvature C X Y (mulSection f Z) = mulSection f (curvature C X Y Z) := by
  apply section_ext; intro p
  have h := TorsionAndMetric.bracket_act X Y f p
  rw [scalarDerivative_global] at h
  simp only [curvature_apply, C.leibniz, map_add, section_add_apply, mulSection_apply]
  rw [h]
  module

theorem tensorial : P202Specs.Geometry.CurvatureAlgebra.tensorialType.{u} := by
  intro n a M _ S C
  exact ⟨curvature_mul_first C, curvature_mul_second C, curvature_mul_third C⟩

/-- Surjective evaluation has a real-linear right inverse. This is only a
choice of extensions of vectors, not a global frame or a trivialization. -/
noncomputable def fieldLift (p : M) : TangentSpace S p →ₗ[ℝ] Field S :=
  Classical.choose ((InducedConnections.sectionEvaluation (tangentBundle S) p).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr
      (section_evaluation_surjective (tangentBundle S) p)))

@[simp] theorem fieldLift_value (p : M) (v : TangentSpace S p) :
    (fieldLift (S := S) p v).val p = v :=
  LinearMap.congr_fun (Classical.choose_spec
    ((InducedConnections.sectionEvaluation (tangentBundle S) p).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr
        (section_evaluation_surjective (tangentBundle S) p)))) v

/-- C∞-linear operators descend from fields to individual tangent vectors. -/
theorem tensorOperator_congr {G : Type*} [AddCommGroup G] [Module ℝ G]
    (p : M) (H : Field S →ₗ[ℝ] G)
    (hH : ∀ (f : GlobalSmooth S) (X : Field S), H (mulSection f X) = f.val p • H X)
    (X Y : Field S) (h : X.val p = Y.val p) : H X = H Y := by
  have hz := TorsionAndMetric.tensorOperator_zero p H hH (X + (-1 : ℝ) • Y) (by
    change X.val p + (-1 : ℝ) • Y.val p = 0
    rw [h]
    module)
  rw [map_add, map_smul, neg_one_smul] at hz
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hz)

theorem curvature_pointwise_first (X X' Y Z : Field S) (p : M)
    (h : X.val p = X'.val p) :
    (curvature C X Y Z).val p = (curvature C X' Y Z).val p := by
  let H : Field S →ₗ[ℝ] TangentSpace S p := {
    toFun := fun U => (curvature C U Y Z).val p
    map_add' := by intros; simp only [curvature_add_first, section_add_apply]
    map_smul' := by intros; simp only [curvature_smul_first, section_smul_apply, RingHom.id_apply] }
  exact tensorOperator_congr (G := TangentSpace S p) p H (fun f U => by
    change (curvature C (mulSection f U) Y Z).val p = _
    rw [curvature_mul_first]; rfl) X X' h

theorem curvature_pointwise_second (X Y Y' Z : Field S) (p : M)
    (h : Y.val p = Y'.val p) :
    (curvature C X Y Z).val p = (curvature C X Y' Z).val p := by
  let H : Field S →ₗ[ℝ] TangentSpace S p := {
    toFun := fun U => (curvature C X U Z).val p
    map_add' := by intros; simp only [curvature_add_second, section_add_apply]
    map_smul' := by intros; simp only [curvature_smul_second, section_smul_apply, RingHom.id_apply] }
  exact tensorOperator_congr (G := TangentSpace S p) p H (fun f U => by
    change (curvature C X (mulSection f U) Z).val p = _
    rw [curvature_mul_second]; rfl) Y Y' h

theorem curvature_pointwise_third (X Y Z Z' : Field S) (p : M)
    (h : Z.val p = Z'.val p) :
    (curvature C X Y Z).val p = (curvature C X Y Z').val p := by
  let H : Field S →ₗ[ℝ] TangentSpace S p := {
    toFun := fun U => (curvature C X Y U).val p
    map_add' := by intros; simp only [curvature_add_third, section_add_apply]
    map_smul' := by intros; simp only [curvature_smul_third, section_smul_apply, RingHom.id_apply] }
  exact tensorOperator_congr (G := TangentSpace S p) p H (fun f U => by
    change (curvature C X Y (mulSection f U)).val p = _
    rw [curvature_mul_third]; rfl) Z Z' h

/-- Curvature with its first two tangent arguments fixed. -/
noncomputable def curvatureThird (p : M) (v w : TangentSpace S p) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S p where
  toFun z := (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z)).val p
  map_add' := by intros; simp only [map_add, curvature_add_third, section_add_apply]
  map_smul' := by intros; simp only [map_smul, curvature_smul_third, section_smul_apply,
    RingHom.id_apply]

noncomputable def curvatureSecond (p : M) (v : TangentSpace S p) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace S p where
  toFun w := curvatureThird C p v w
  map_add' := by
    intro w x
    apply LinearMap.ext; intro z
    change (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p (w + x)) (fieldLift (S := S) p z)).val p =
      (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z)).val p +
      (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p x) (fieldLift (S := S) p z)).val p
    simp only [map_add, curvature_add_second, section_add_apply]
  map_smul' := by
    intro c w
    apply LinearMap.ext; intro z
    change (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p (c • w)) (fieldLift (S := S) p z)).val p =
      c • (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z)).val p
    simp only [map_smul, curvature_smul_second, section_smul_apply]

/-- The trilinear curvature map on each original tangent fiber. -/
noncomputable def curvatureFiber (p : M) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ]
      TangentSpace S p →ₗ[ℝ] TangentSpace S p where
  toFun v := curvatureSecond C p v
  map_add' := by
    intro v w
    apply LinearMap.ext; intro z
    apply LinearMap.ext; intro t
    change (curvature C (fieldLift (S := S) p (v + w)) (fieldLift (S := S) p z) (fieldLift (S := S) p t)).val p =
      (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p z) (fieldLift (S := S) p t)).val p +
      (curvature C (fieldLift (S := S) p w) (fieldLift (S := S) p z) (fieldLift (S := S) p t)).val p
    simp only [map_add, curvature_add_first, section_add_apply]
  map_smul' := by
    intro c v
    apply LinearMap.ext; intro z
    apply LinearMap.ext; intro t
    change (curvature C (fieldLift (S := S) p (c • v)) (fieldLift (S := S) p z) (fieldLift (S := S) p t)).val p =
      c • (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p z) (fieldLift (S := S) p t)).val p
    simp only [map_smul, curvature_smul_first, section_smul_apply]

@[simp] theorem curvatureFiber_apply (X Y Z : Field S) (p : M) :
    curvatureFiber C p (X.val p) (Y.val p) (Z.val p) = (curvature C X Y Z).val p := by
  change (curvature C (fieldLift (S := S) p (X.val p)) (fieldLift (S := S) p (Y.val p))
    (fieldLift (S := S) p (Z.val p))).val p = _
  rw [curvature_pointwise_first C _ X _ _ p (fieldLift_value p _),
    curvature_pointwise_second C X _ Y _ p (fieldLift_value p _),
    curvature_pointwise_third C X Y _ Z p (fieldLift_value p _)]

noncomputable def curvatureTensor : CurvatureTensor S where
  val := curvatureFiber C
  smooth X Y Z := by
    have he : (fun p => curvatureFiber C p (X.val p) (Y.val p) (Z.val p)) =
        (curvature C X Y Z).val := funext (curvatureFiber_apply C X Y Z)
    rw [he]
    exact (curvature C X Y Z).property

theorem curvatureTensor_ext {T U : CurvatureTensor S} (h : T.val = U.val) : T = U := by
  cases T; cases U; cases h; rfl

theorem tensor_exists_unique : P202Specs.Geometry.CurvatureAlgebra.tensor_exists_uniqueType.{u} := by
  intro n a M _ S C
  refine ⟨curvatureTensor C, curvatureFiber_apply C, ?_⟩
  intro T hT
  have he : T.val = (curvatureTensor C).val := by
    funext p
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro z
    change T.val p v w z =
      (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z)).val p
    have h := hT (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z) p
    simpa only [fieldLift_value] using h
  exact curvatureTensor_ext he

/-- Jacobi for the canonical intrinsic bracket. -/
theorem bracket_jacobi (X Y Z : Field S) :
    bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0 := by
  apply section_ext; intro p
  exact ((SmoothManifolds.LieBrackets.bracket_algebra S (tangentStructure S)).2.2
    _ TorsionAndMetric.originalBracket_rule).2.1
    (originalField S X) (originalField S Y) (originalField S Z) p

/-- Torsion freeness, as an identity of smooth fields. -/
theorem bracket_cov (hC : IsTorsionFree C) (X Y : Field S) :
    bracket X Y = C.cov X Y + (-1 : ℝ) • C.cov Y X := by
  apply section_ext; intro p
  have h := TorsionAndMetric.torsion_apply C X Y p
  change (P202.TorsionMetricData.torsion C X Y).val p = _ at h
  rw [hC X Y] at h
  change 0 = _ at h
  simp only [section_add_apply, section_smul_apply, neg_one_smul]
  exact (sub_eq_zero.mp h.symm).symm

/-- The first Bianchi identity follows from torsion freeness and Jacobi. -/
theorem field_first_bianchi (hC : IsTorsionFree C) (X Y Z : Field S) :
    curvature C X Y Z + curvature C Y Z X + curvature C Z X Y = 0 := by
  calc
    _ = bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) := by
      rw [bracket_cov C hC X (bracket Y Z), bracket_cov C hC Y (bracket Z X),
        bracket_cov C hC Z (bracket X Y)]
      rw [bracket_cov C hC Y Z, bracket_cov C hC Z X, bracket_cov C hC X Y]
      simp only [curvature, P202.CurvatureData.curvature, bracket_cov C hC, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply]
      module
    _ = 0 := bracket_jacobi X Y Z

/-- The metric product rule as an identity of globally smooth functions. -/
theorem metric_act (g : RiemannianMetric S) (hc : IsMetricCompatible g C)
    (X Y Z : Field S) :
    act S X (LeviCivita.fieldPairing g Y Z) =
      LeviCivita.fieldPairing g (C.cov X Y) Z +
        LeviCivita.fieldPairing g Y (C.cov X Z) := by
  apply Subtype.ext; funext p
  rw [← scalarDerivative_global]
  exact hc X Y Z p

/-- The scalar commutator applied to the metric pairing. -/
theorem field_metric_skew (g : RiemannianMetric S) (hc : IsMetricCompatible g C)
    (X Y Z W : Field S) (p : M) :
    pairing g p ((curvature C X Y Z).val p) (W.val p) +
      pairing g p (Z.val p) ((curvature C X Y W).val p) = 0 := by
  have he : act S (bracket X Y) (LeviCivita.fieldPairing g Z W) =
      act S X (act S Y (LeviCivita.fieldPairing g Z W)) -
        act S Y (act S X (LeviCivita.fieldPairing g Z W)) := by
    apply Subtype.ext; funext q
    exact (scalarDerivative_global _ _ _).symm.trans
      (TorsionAndMetric.bracket_act X Y (LeviCivita.fieldPairing g Z W) q)
  simp only [metric_act C g hc, map_add] at he
  have h := congrArg (fun f : GlobalSmooth S => f.val p) he
  simp only [LeviCivita.fieldPairing_apply, Subalgebra.coe_add, Subalgebra.coe_sub,
    Pi.add_apply, Pi.sub_apply] at h
  simp only [curvature_apply, LeviCivita.tangent_sub_as_add, pairing,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  simp only [pairing] at h
  linarith

theorem represents_apply (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (X Y Z : Field S) (p : M) :
    T.val p (X.val p) (Y.val p) (Z.val p) = (curvature C X Y Z).val p := hT X Y Z p

theorem tensor_first_bianchi (hC : IsTorsionFree C) (T : CurvatureTensor S)
    (hT : RepresentsCurvature C T) (p : M) (v w z : TangentSpace S p) :
    T.val p v w z + T.val p w z v + T.val p z v w = 0 := by
  have h := congrArg (fun X : Field S => X.val p)
    (field_first_bianchi C hC (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z))
  simpa only [section_add_apply, section_zero_apply, ← represents_apply C T hT, fieldLift_value] using h

theorem form_skew_first (g : RiemannianMetric S) (T : CurvatureTensor S)
    (hT : RepresentsCurvature C T) (p : M) (v w z t : TangentSpace S p) :
    curvatureForm g T p v w z t = -curvatureForm g T p w v z t := by
  have h := congrArg (fun X : Field S => X.val p)
    (curvature_skew C (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z))
  change (curvature C (fieldLift (S := S) p v) (fieldLift (S := S) p w)
    (fieldLift (S := S) p z)).val p = (-1 : ℝ) •
    (curvature C (fieldLift (S := S) p w) (fieldLift (S := S) p v)
      (fieldLift (S := S) p z)).val p at h
  rw [← hT (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z) p,
    ← hT (fieldLift (S := S) p w) (fieldLift (S := S) p v) (fieldLift (S := S) p z) p] at h
  simp only [fieldLift_value] at h
  unfold curvatureForm P202.CurvatureData.curvatureForm
  rw [h]
  simp only [pairing, LinearMap.BilinForm.smul_left, neg_one_mul]

theorem form_skew_last (g : RiemannianMetric S) (hc : IsMetricCompatible g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (p : M) (v w z t : TangentSpace S p) :
    curvatureForm g T p v w z t = -curvatureForm g T p v w t z := by
  have h := field_metric_skew C g hc (fieldLift (S := S) p v) (fieldLift (S := S) p w)
    (fieldLift (S := S) p z) (fieldLift (S := S) p t) p
  rw [← hT (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p z) p,
    ← hT (fieldLift (S := S) p v) (fieldLift (S := S) p w) (fieldLift (S := S) p t) p] at h
  simp only [fieldLift_value] at h
  simp only [pairing] at h
  rw [g.symmetric p z (T.val p v w t)] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Pair interchange is an algebraic consequence of the two skew symmetries
and the first Bianchi identity; no normal-coordinate hypotheses are needed. -/
theorem form_pair_exchange (g : RiemannianMetric S) (hc : IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (p : M) (v w z t : TangentSpace S p) :
    curvatureForm g T p v w z t = curvatureForm g T p z t v w := by
  have hb (x y z w : TangentSpace S p) :
      curvatureForm g T p x y z w + curvatureForm g T p y z x w +
        curvatureForm g T p z x y w = 0 := by
    have h := congrArg (fun v => pairing g p v w) (tensor_first_bianchi C hc.1 T hT p x y z)
    simpa only [curvatureForm, P202.CurvatureData.curvatureForm, pairing, map_add,
      LinearMap.add_apply, map_zero, LinearMap.zero_apply] using h
  have hs := form_skew_first C g T hT p
  have ht := form_skew_last C g hc.2 T hT p
  linarith only [
    hb v w z t, hb v w t z, hb v z w t,
    hb v z t w, hb v t w z, hb v t z w,
    hb w v z t, hb w v t z, hb w z v t,
    hb w z t v, hb w t v z, hb w t z v,
    hb z v w t, hb z v t w, hb z w v t,
    hb z w t v, hb z t v w, hb z t w v,
    hb t v w z, hb t v z w, hb t w v z,
    hb t w z v, hb t z v w, hb t z w v,
    hs v w z t, hs v w t z, hs v z w t,
    hs v z t w, hs v t w z, hs v t z w,
    hs w v z t, hs w v t z, hs w z v t,
    hs w z t v, hs w t v z, hs w t z v,
    hs z v w t, hs z v t w, hs z w v t,
    hs z w t v, hs z t v w, hs z t w v,
    hs t v w z, hs t v z w, hs t w v z,
    hs t w z v, hs t z v w, hs t z w v,
    ht v w z t, ht v w t z, ht v z w t,
    ht v z t w, ht v t w z, ht v t z w,
    ht w v z t, ht w v t z, ht w z v t,
    ht w z t v, ht w t v z, ht w t z v,
    ht z v w t, ht z v t w, ht z w v t,
    ht z w t v, ht z t v w, ht z t w v,
    ht t v w z, ht t v z w, ht t w v z,
    ht t w z v, ht t z v w, ht t z w v]

theorem first_bianchi : P202Specs.Geometry.CurvatureAlgebra.first_bianchiType.{u} := by
  intro n a M _ S g C hc T hT p v w z
  exact tensor_first_bianchi C hc.1 T hT p v w z

theorem symmetries : P202Specs.Geometry.CurvatureAlgebra.symmetriesType.{u} := by
  intro n a M _ S g C hc T hT p v w z t
  exact ⟨form_skew_first C g T hT p v w z t,
    form_skew_last C g hc.2 T hT p v w z t,
    form_pair_exchange C g hc T hT p v w z t⟩

section Sectional
variable (g : RiemannianMetric S) (hc : IsLeviCivita g C)
  (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)

@[simp] theorem form_add_first (v w x y z : TangentSpace S p) :
    curvatureForm g T p (v + w) x y z =
      curvatureForm g T p v x y z + curvatureForm g T p w x y z := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_add, LinearMap.add_apply]

@[simp] theorem form_add_second (v w x y z : TangentSpace S p) :
    curvatureForm g T p v (w + x) y z =
      curvatureForm g T p v w y z + curvatureForm g T p v x y z := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_add, LinearMap.add_apply]

@[simp] theorem form_add_third (v w x y z : TangentSpace S p) :
    curvatureForm g T p v w (x + y) z =
      curvatureForm g T p v w x z + curvatureForm g T p v w y z := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_add, LinearMap.add_apply]

@[simp] theorem form_add_fourth (v w x y z : TangentSpace S p) :
    curvatureForm g T p v w x (y + z) =
      curvatureForm g T p v w x y + curvatureForm g T p v w x z := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_add]

@[simp] theorem form_smul_first (c : ℝ) (v w x y : TangentSpace S p) :
    curvatureForm g T p (c • v) w x y = c * curvatureForm g T p v w x y := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem form_smul_second (c : ℝ) (v w x y : TangentSpace S p) :
    curvatureForm g T p v (c • w) x y = c * curvatureForm g T p v w x y := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem form_smul_third (c : ℝ) (v w x y : TangentSpace S p) :
    curvatureForm g T p v w (c • x) y = c * curvatureForm g T p v w x y := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem form_smul_fourth (c : ℝ) (v w x y : TangentSpace S p) :
    curvatureForm g T p v w x (c • y) = c * curvatureForm g T p v w x y := by
  simp only [curvatureForm, P202.CurvatureData.curvatureForm, pairing,
    map_smul, smul_eq_mul]

include C hT in
theorem form_self_first (v z t : TangentSpace S p) :
    curvatureForm g T p v v z t = 0 := by
  linarith only [form_skew_first C g T hT p v v z t]

include C hc hT in
theorem form_self_last (v w z : TangentSpace S p) :
    curvatureForm g T p v w z z = 0 := by
  linarith only [form_skew_last C g hc.2 T hT p v w z z]

include C hT in
theorem form_change_first_two (a b c d : ℝ) (v w z t : TangentSpace S p) :
    curvatureForm g T p (a • v + b • w) (c • v + d • w) z t =
      (a * d - b * c) * curvatureForm g T p v w z t := by
  simp only [form_add_first, form_add_second, form_smul_first, form_smul_second,
    form_self_first C g T hT, form_skew_first C g T hT p w v z t]
  ring

include C hc hT in
theorem sectional_numerator_change (a b c d : ℝ) (v w : TangentSpace S p) :
    curvatureForm g T p (a • v + b • w) (c • v + d • w)
      (c • v + d • w) (a • v + b • w) =
      (a * d - b * c) ^ 2 * curvatureForm g T p v w w v := by
  rw [form_change_first_two C g T hT p a b c d]
  simp only [form_add_third, form_add_fourth, form_smul_third, form_smul_fourth,
    form_self_last C g hc T hT, form_skew_last C g hc.2 T hT p v w v w]
  ring

/-- Both numerator and metric Gram determinant transform by det². -/
theorem gram_change (a b c d : ℝ) (v w : TangentSpace S p) :
    pairing g p (a • v + b • w) (a • v + b • w) *
      pairing g p (c • v + d • w) (c • v + d • w) -
      pairing g p (a • v + b • w) (c • v + d • w) ^ 2 =
    (a * d - b * c) ^ 2 *
      (pairing g p v v * pairing g p w w - pairing g p v w ^ 2) := by
  simp only [pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  rw [g.symmetric p w v]
  ring

end Sectional

/-- An independent transformed pair has a nonsingular coefficient matrix. -/
theorem change_det_ne_zero (p : M) (v w : TangentSpace S p) (a b c d : ℝ)
    (h : LinearIndependent ℝ ![a • v + b • w, c • v + d • w]) : a * d - b * c ≠ 0 := by
  have hh := (linearIndependent_fin2 (K := ℝ)
    (f := ![a • v + b • w, c • v + d • w])).mp h
  change c • v + d • w ≠ 0 ∧
    (∀ t : ℝ, t • (c • v + d • w) ≠ a • v + b • w) at hh
  intro hz
  by_cases hd : d = 0
  · subst d
    have hbc : b * c = 0 := by linarith
    have hc : c ≠ 0 := by
      intro hc; simp only [hc, zero_smul, add_zero] at hh
      exact hh.1 rfl
    have hb : b = 0 := (mul_eq_zero.mp hbc).resolve_right hc
    apply hh.2 (a / c)
    rw [hb]
    simp only [zero_smul, add_zero, smul_smul]
    rw [div_mul_cancel₀ _ hc]
  · apply hh.2 (b / d)
    have ha : b / d * c = a := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff hd).mpr
      nlinarith
    simp only [smul_add, smul_smul, ha, div_mul_cancel₀ _ hd]

theorem sectional_basis_independent :
    P202Specs.Geometry.CurvatureAlgebra.sectional_basis_independentType.{u} := by
  intro n a M _ S g C hc T hT p X Y U V hXY hUV hspan
  have hU : U ∈ Submodule.span ℝ ({X, Y} : Set (TangentSpace S p)) := by
    rw [hspan]; exact Submodule.subset_span (by simp)
  have hV : V ∈ Submodule.span ℝ ({X, Y} : Set (TangentSpace S p)) := by
    rw [hspan]; exact Submodule.subset_span (by simp)
  obtain ⟨a, b, ha⟩ := Submodule.mem_span_pair.mp hU
  obtain ⟨c, d, hb⟩ := Submodule.mem_span_pair.mp hV
  have hd : a * d - b * c ≠ 0 := change_det_ne_zero p X Y a b c d (by simpa [ha, hb] using hUV)
  unfold P202.CurvatureData.sectionalCurvature
  rw [← ha, ← hb]
  have hn : P202.CurvatureData.curvatureForm g T p (a • X + b • Y) (c • X + d • Y)
      (c • X + d • Y) (a • X + b • Y) =
      (a * d - b * c) ^ 2 * P202.CurvatureData.curvatureForm g T p X Y Y X :=
    sectional_numerator_change C g hc T hT p a b c d X Y
  rw [hn, gram_change g p a b c d X Y]
  exact (mul_div_mul_left _ _ (pow_ne_zero 2 hd)).symm

/-- Test-field smoothness gives ordinary smooth coordinate components. -/
theorem tensor_coordinates_smooth (T : CurvatureTensor S)
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S) (j k l : Fin n)
    (p : M) (hp : p ∈ (tangentBundle S).baseSet i) :
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q => ((tangentBundle S).trivialization i
        ⟨q, T.val q
          (((tangentBundle S).trivialization i).symm q (Pi.single j 1))
          (((tangentBundle S).trivialization i).symm q (Pi.single k 1))
          (((tangentBundle S).trivialization i).symm q (Pi.single l 1))⟩).2) p := by
  let B := tangentBundle S
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hp⟩
  have h := SmoothManifolds.SectionExtension.coordinates_smoothAt B i hp
    (T.smooth (e j) (e k) (e l) p)
  apply h.congr
  filter_upwards [ho.mem_nhds hp, he j, he k, he l] with q hq hj hk hl
  rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq] at hj hk hl
  have hb (m : Fin n) : b.section_ m ⟨q, hq⟩ =
      (B.trivialization i).symm q (Pi.single m 1) := by
    change (B.fiberCoordinates i q hq).symm ((Pi.basisFun ℝ (Fin n)) m) = _
    rw [Pi.basisFun_apply, SmoothVectorBundle.fiberCoordinates_symm_apply]
  rw [hj, hk, hl, hb, hb, hb]

end P202.Geometry.CurvatureAlgebra
