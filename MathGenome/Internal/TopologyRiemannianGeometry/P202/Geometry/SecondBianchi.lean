import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SecondBianchi
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.Geometry.SecondBianchi
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.TorsionMetricData
  P202.LeviCivitaData P202.CurvatureData P202.SecondBianchiData
open ConnectionForms (section_ext section_add_apply section_smul_apply section_zero_apply
  mulSection_apply section_evaluation_surjective)
open CurvatureAlgebra (fieldLift fieldLift_value tensorOperator_congr)
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable abbrev covariantDerivative := @P202.SecondBianchiData.covariantDerivative

@[simp] theorem tensorSection_apply (T : CurvatureTensor S) (Y Z W : Field S) (p : M) :
    (tensorSection T Y Z W).val p = T.val p (Y.val p) (Z.val p) (W.val p) := rfl

@[simp] theorem tensorSection_add_first (T : CurvatureTensor S) (Y U Z W : Field S) :
    tensorSection T (Y + U) Z W = tensorSection T Y Z W + tensorSection T U Z W := by
  apply section_ext; intro p
  simp only [tensorSection_apply, section_add_apply, map_add, LinearMap.add_apply]

@[simp] theorem tensorSection_add_second (T : CurvatureTensor S) (Y Z U W : Field S) :
    tensorSection T Y (Z + U) W = tensorSection T Y Z W + tensorSection T Y U W := by
  apply section_ext; intro p
  simp only [tensorSection_apply, section_add_apply, map_add, LinearMap.add_apply]

@[simp] theorem tensorSection_add_third (T : CurvatureTensor S) (Y Z W U : Field S) :
    tensorSection T Y Z (W + U) = tensorSection T Y Z W + tensorSection T Y Z U := by
  apply section_ext; intro p
  simp only [tensorSection_apply, section_add_apply, map_add]

@[simp] theorem tensorSection_smul_first (T : CurvatureTensor S) (c : ℝ) (Y Z W : Field S) :
    tensorSection T (c • Y) Z W = c • tensorSection T Y Z W := by
  apply section_ext; intro p
  simp only [tensorSection_apply, section_smul_apply, map_smul, LinearMap.smul_apply]

@[simp] theorem tensorSection_smul_second (T : CurvatureTensor S) (c : ℝ) (Y Z W : Field S) :
    tensorSection T Y (c • Z) W = c • tensorSection T Y Z W := by
  apply section_ext; intro p
  simp only [tensorSection_apply, section_smul_apply, map_smul, LinearMap.smul_apply]

@[simp] theorem tensorSection_smul_third (T : CurvatureTensor S) (c : ℝ) (Y Z W : Field S) :
    tensorSection T Y Z (c • W) = c • tensorSection T Y Z W := by
  apply section_ext; intro p
  simp only [tensorSection_apply, section_smul_apply, map_smul]

@[simp] theorem tensorSection_mul_first (T : CurvatureTensor S) (f : GlobalSmooth S)
    (Y Z W : Field S) :
    tensorSection T (mulSection f Y) Z W = mulSection f (tensorSection T Y Z W) := by
  apply section_ext; intro p
  simp only [tensorSection_apply, mulSection_apply, map_smul, LinearMap.smul_apply]

@[simp] theorem tensorSection_mul_second (T : CurvatureTensor S) (f : GlobalSmooth S)
    (Y Z W : Field S) :
    tensorSection T Y (mulSection f Z) W = mulSection f (tensorSection T Y Z W) := by
  apply section_ext; intro p
  simp only [tensorSection_apply, mulSection_apply, map_smul, LinearMap.smul_apply]

@[simp] theorem tensorSection_mul_third (T : CurvatureTensor S) (f : GlobalSmooth S)
    (Y Z W : Field S) :
    tensorSection T Y Z (mulSection f W) = mulSection f (tensorSection T Y Z W) := by
  apply section_ext; intro p
  simp only [tensorSection_apply, mulSection_apply, map_smul]

theorem derivativeField_add_first (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) :
    tensorDerivativeField C T (X + U) Y Z W = tensorDerivativeField C T X Y Z W + tensorDerivativeField C T U Y Z W := by
  simp only [tensorDerivativeField, tensorSection_add_first, tensorSection_add_second,
    tensorSection_add_third, map_add, LinearMap.add_apply]
  module

theorem derivativeField_smul_first (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (c : ℝ) (X Y Z W : Field S) :
    tensorDerivativeField C T (c • X) Y Z W = c • tensorDerivativeField C T X Y Z W := by
  simp only [tensorDerivativeField, tensorSection_smul_first, tensorSection_smul_second,
    tensorSection_smul_third, map_smul, LinearMap.smul_apply]
  module

theorem derivativeField_mul_first (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (f : GlobalSmooth S) (X Y Z W : Field S) :
    tensorDerivativeField C T (mulSection f X) Y Z W = mulSection f (tensorDerivativeField C T X Y Z W) := by
  apply section_ext; intro p
  simp only [tensorDerivativeField, C.linear_field, tensorSection_mul_first,
    tensorSection_mul_second, tensorSection_mul_third, section_add_apply, section_smul_apply,
    mulSection_apply]
  module

theorem derivativeField_add_second (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) :
    tensorDerivativeField C T X (Y + U) Z W = tensorDerivativeField C T X Y Z W + tensorDerivativeField C T X U Z W := by
  simp only [tensorDerivativeField, tensorSection_add_first, map_add]
  module

theorem derivativeField_smul_second (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (c : ℝ) (X Y Z W : Field S) :
    tensorDerivativeField C T X (c • Y) Z W = c • tensorDerivativeField C T X Y Z W := by
  simp only [tensorDerivativeField, tensorSection_smul_first, map_smul]
  module

theorem derivativeField_mul_second (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (f : GlobalSmooth S) (X Y Z W : Field S) :
    tensorDerivativeField C T X (mulSection f Y) Z W = mulSection f (tensorDerivativeField C T X Y Z W) := by
  apply section_ext; intro p
  simp only [tensorDerivativeField, C.leibniz, tensorSection_add_first, tensorSection_mul_first,
    section_add_apply, section_smul_apply, mulSection_apply]
  module

theorem derivativeField_add_third (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) :
    tensorDerivativeField C T X Y (Z + U) W = tensorDerivativeField C T X Y Z W + tensorDerivativeField C T X Y U W := by
  simp only [tensorDerivativeField, tensorSection_add_second, map_add]
  module

theorem derivativeField_smul_third (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (c : ℝ) (X Y Z W : Field S) :
    tensorDerivativeField C T X Y (c • Z) W = c • tensorDerivativeField C T X Y Z W := by
  simp only [tensorDerivativeField, tensorSection_smul_second, map_smul]
  module

theorem derivativeField_mul_third (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (f : GlobalSmooth S) (X Y Z W : Field S) :
    tensorDerivativeField C T X Y (mulSection f Z) W = mulSection f (tensorDerivativeField C T X Y Z W) := by
  apply section_ext; intro p
  simp only [tensorDerivativeField, C.leibniz, tensorSection_add_second, tensorSection_mul_second,
    section_add_apply, section_smul_apply, mulSection_apply]
  module

theorem derivativeField_add_fourth (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) :
    tensorDerivativeField C T X Y Z (W + U) = tensorDerivativeField C T X Y Z W + tensorDerivativeField C T X Y Z U := by
  simp only [tensorDerivativeField, tensorSection_add_third, map_add]
  module

theorem derivativeField_smul_fourth (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (c : ℝ) (X Y Z W : Field S) :
    tensorDerivativeField C T X Y Z (c • W) = c • tensorDerivativeField C T X Y Z W := by
  simp only [tensorDerivativeField, tensorSection_smul_third, map_smul]
  module

theorem derivativeField_mul_fourth (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (f : GlobalSmooth S) (X Y Z W : Field S) :
    tensorDerivativeField C T X Y Z (mulSection f W) = mulSection f (tensorDerivativeField C T X Y Z W) := by
  apply section_ext; intro p
  simp only [tensorDerivativeField, C.leibniz, tensorSection_add_third, tensorSection_mul_third,
    section_add_apply, section_smul_apply, mulSection_apply]
  module

theorem derivativeField_pointwise_first (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) (p : M)
    (h : X.val p = U.val p) :
    (tensorDerivativeField C T X Y Z W).val p =
      (tensorDerivativeField C T U Y Z W).val p := by
  let H : Field S →ₗ[ℝ] TangentSpace S p := {
    toFun := fun U => (tensorDerivativeField C T U Y Z W).val p
    map_add' := by intros; simp only [derivativeField_add_first, section_add_apply]
    map_smul' := by intros; simp only [derivativeField_smul_first, section_smul_apply,
      RingHom.id_apply] }
  exact tensorOperator_congr (G := TangentSpace S p) p H (fun f U => by
    change (tensorDerivativeField C T (mulSection f U) Y Z W).val p = _
    rw [derivativeField_mul_first]; rfl) X U h

theorem derivativeField_pointwise_second (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) (p : M)
    (h : Y.val p = U.val p) :
    (tensorDerivativeField C T X Y Z W).val p =
      (tensorDerivativeField C T X U Z W).val p := by
  let H : Field S →ₗ[ℝ] TangentSpace S p := {
    toFun := fun U => (tensorDerivativeField C T X U Z W).val p
    map_add' := by intros; simp only [derivativeField_add_second, section_add_apply]
    map_smul' := by intros; simp only [derivativeField_smul_second, section_smul_apply,
      RingHom.id_apply] }
  exact tensorOperator_congr (G := TangentSpace S p) p H (fun f U => by
    change (tensorDerivativeField C T X (mulSection f U) Z W).val p = _
    rw [derivativeField_mul_second]; rfl) Y U h

theorem derivativeField_pointwise_third (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) (p : M)
    (h : Z.val p = U.val p) :
    (tensorDerivativeField C T X Y Z W).val p =
      (tensorDerivativeField C T X Y U W).val p := by
  let H : Field S →ₗ[ℝ] TangentSpace S p := {
    toFun := fun U => (tensorDerivativeField C T X Y U W).val p
    map_add' := by intros; simp only [derivativeField_add_third, section_add_apply]
    map_smul' := by intros; simp only [derivativeField_smul_third, section_smul_apply,
      RingHom.id_apply] }
  exact tensorOperator_congr (G := TangentSpace S p) p H (fun f U => by
    change (tensorDerivativeField C T X Y (mulSection f U) W).val p = _
    rw [derivativeField_mul_third]; rfl) Z U h

theorem derivativeField_pointwise_fourth (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W U : Field S) (p : M)
    (h : W.val p = U.val p) :
    (tensorDerivativeField C T X Y Z W).val p =
      (tensorDerivativeField C T X Y Z U).val p := by
  let H : Field S →ₗ[ℝ] TangentSpace S p := {
    toFun := fun U => (tensorDerivativeField C T X Y Z U).val p
    map_add' := by intros; simp only [derivativeField_add_fourth, section_add_apply]
    map_smul' := by intros; simp only [derivativeField_smul_fourth, section_smul_apply,
      RingHom.id_apply] }
  exact tensorOperator_congr (G := TangentSpace S p) p H (fun f U => by
    change (tensorDerivativeField C T X Y Z (mulSection f U)).val p = _
    rw [derivativeField_mul_fourth]; rfl) W U h

/-- A concrete multilinear descent, using linear choices of smooth extensions.
The evaluation theorem below proves that the choice has no effect. -/
noncomputable def derivativeFiber (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (p : M) : FiberDerivative S p :=
  { toFun := fun x =>
    { toFun := fun y =>
      { toFun := fun z =>
        { toFun := fun w =>
            (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p
          map_add' := by
            intro v v'
            change (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p (v + v'))).val p =
              (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p v)).val p +
              (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p v')).val p
            simp only [map_add, derivativeField_add_fourth, section_add_apply]
          map_smul' := by
            intro c v
            change (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p (c • v))).val p =
              c • (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p v)).val p
            simp only [map_smul, derivativeField_smul_fourth, section_smul_apply]
        }
        map_add' := by
          intro v v'
          apply LinearMap.ext; intro w
          change (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p (v + v')) (fieldLift (S := S) p w)).val p =
            (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p v) (fieldLift (S := S) p w)).val p +
            (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p v') (fieldLift (S := S) p w)).val p
          simp only [map_add, derivativeField_add_third, section_add_apply]
        map_smul' := by
          intro c v
          apply LinearMap.ext; intro w
          change (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p (c • v)) (fieldLift (S := S) p w)).val p =
            c • (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p y) (fieldLift (S := S) p v) (fieldLift (S := S) p w)).val p
          simp only [map_smul, derivativeField_smul_third, section_smul_apply]
      }
      map_add' := by
        intro v v'
        apply LinearMap.ext; intro z
        apply LinearMap.ext; intro w
        change (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p (v + v')) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p =
          (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p v) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p +
          (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p v') (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p
        simp only [map_add, derivativeField_add_second, section_add_apply]
      map_smul' := by
        intro c v
        apply LinearMap.ext; intro z
        apply LinearMap.ext; intro w
        change (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p (c • v)) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p =
          c • (tensorDerivativeField C T (fieldLift (S := S) p x) (fieldLift (S := S) p v) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p
        simp only [map_smul, derivativeField_smul_second, section_smul_apply]
    }
    map_add' := by
      intro v v'
      apply LinearMap.ext; intro y
      apply LinearMap.ext; intro z
      apply LinearMap.ext; intro w
      change (tensorDerivativeField C T (fieldLift (S := S) p (v + v')) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p =
        (tensorDerivativeField C T (fieldLift (S := S) p v) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p +
        (tensorDerivativeField C T (fieldLift (S := S) p v') (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p
      simp only [map_add, derivativeField_add_first, section_add_apply]
    map_smul' := by
      intro c v
      apply LinearMap.ext; intro y
      apply LinearMap.ext; intro z
      apply LinearMap.ext; intro w
      change (tensorDerivativeField C T (fieldLift (S := S) p (c • v)) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p =
        c • (tensorDerivativeField C T (fieldLift (S := S) p v) (fieldLift (S := S) p y) (fieldLift (S := S) p z) (fieldLift (S := S) p w)).val p
      simp only [map_smul, derivativeField_smul_first, section_smul_apply]
  }

theorem derivativeFiber_rule (C : Connection (tangentBundle S)) (T : CurvatureTensor S)
    (p : M) : InducedDerivativeRule C T p (derivativeFiber C T p) := by
  intro X Y Z W
  change (tensorDerivativeField C T (fieldLift (S := S) p (X.val p))
    (fieldLift (S := S) p (Y.val p)) (fieldLift (S := S) p (Z.val p))
    (fieldLift (S := S) p (W.val p))).val p = _
  rw [derivativeField_pointwise_first C T _ _ _ _ X p (fieldLift_value p _),
    derivativeField_pointwise_second C T _ _ _ _ Y p (fieldLift_value p _),
    derivativeField_pointwise_third C T _ _ _ _ Z p (fieldLift_value p _),
    derivativeField_pointwise_fourth C T _ _ _ _ W p (fieldLift_value p _)]

theorem derivative_rule : P202Specs.Geometry.SecondBianchi.derivative_ruleType.{u} := by
  intro n a M _ S C T p
  have hex : ∃ D : FiberDerivative S p, InducedDerivativeRule C T p D :=
    ⟨derivativeFiber C T p, derivativeFiber_rule C T p⟩
  have hr : InducedDerivativeRule C T p (covariantDerivative C T p) := by
    simpa only [covariantDerivative, P202.SecondBianchiData.covariantDerivative,
      dite_eq_left hex] using Classical.choose_spec hex
  refine ⟨hr, ?_⟩
  intro D hD
  ext x y z w
  obtain ⟨X, rfl⟩ := section_evaluation_surjective (tangentBundle S) p x
  obtain ⟨Y, rfl⟩ := section_evaluation_surjective (tangentBundle S) p y
  obtain ⟨Z, rfl⟩ := section_evaluation_surjective (tangentBundle S) p z
  obtain ⟨W, rfl⟩ := section_evaluation_surjective (tangentBundle S) p w
  rw [hD, hr]

theorem derivative_smooth : P202Specs.Geometry.SecondBianchi.derivative_smoothType.{u} := by
  intro n a M _ S C T X Y Z W
  have he : (fun p => covariantDerivative C T p (X.val p) (Y.val p) (Z.val p) (W.val p)) =
      (tensorDerivativeField C T X Y Z W).val :=
    funext (fun p => (derivative_rule C T p).1 X Y Z W)
  rw [he]
  exact (tensorDerivativeField C T X Y Z W).property

theorem tensorSection_eq_curvature (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (Y Z W : Field S) :
    tensorSection T Y Z W = curvature C Y Z W := by
  apply section_ext; intro p
  exact hT Y Z W p

/-- The covariant exterior Bianchi identity follows solely from the two
Jacobi identities (for operators and for vector fields). No torsion or metric
hypothesis is needed for this intermediate identity. -/
theorem exterior_bianchi (C : Connection (tangentBundle S)) (X Y Z W : Field S) :
    (C.cov X (curvature C Y Z W) + (-1 : ℝ) • curvature C Y Z (C.cov X W) +
      curvature C X (bracket Y Z) W) +
    (C.cov Y (curvature C Z X W) + (-1 : ℝ) • curvature C Z X (C.cov Y W) +
      curvature C Y (bracket Z X) W) +
    (C.cov Z (curvature C X Y W) + (-1 : ℝ) • curvature C X Y (C.cov Z W) +
      curvature C Z (bracket X Y) W) = 0 := by
  calc
    _ = (-1 : ℝ) • C.cov (bracket X (bracket Y Z) +
        bracket Y (bracket Z X) + bracket Z (bracket X Y)) W := by
      simp only [curvature, P202.CurvatureData.curvature, map_add, map_smul,
        LinearMap.add_apply]
      module
    _ = 0 := by rw [CurvatureAlgebra.bracket_jacobi, map_zero, LinearMap.zero_apply, smul_zero]

/-- Torsion freeness converts the exterior identity into the cyclic identity
for the induced tensor connection. -/
theorem field_second_bianchi (C : Connection (tangentBundle S)) (hC : IsTorsionFree C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (X Y Z W : Field S) :
    tensorDerivativeField C T X Y Z W + tensorDerivativeField C T Y Z X W +
      tensorDerivativeField C T Z X Y W = 0 := by
  have he := exterior_bianchi C X Y Z W
  rw [CurvatureAlgebra.bracket_cov C hC Y Z, CurvatureAlgebra.bracket_cov C hC Z X,
    CurvatureAlgebra.bracket_cov C hC X Y] at he
  simp only [CurvatureAlgebra.curvature_add_second, CurvatureAlgebra.curvature_smul_second] at he
  simp only [tensorDerivativeField, tensorSection_eq_curvature C T hT]
  have hs (A B : Field S) : curvature C A B W = (-1 : ℝ) • curvature C B A W :=
    CurvatureAlgebra.curvature_skew C A B W
  rw [hs (C.cov X Y) Z, hs (C.cov Y Z) X, hs (C.cov Z X) Y]
  simp only [CurvatureAlgebra.curvature] at he
  calc
    _ = (C.cov X (curvature C Y Z W) + (-1 : ℝ) • curvature C Y Z (C.cov X W) +
        (curvature C X (C.cov Y Z) W + (-1 : ℝ) • curvature C X (C.cov Z Y) W)) +
      (C.cov Y (curvature C Z X W) + (-1 : ℝ) • curvature C Z X (C.cov Y W) +
        (curvature C Y (C.cov Z X) W + (-1 : ℝ) • curvature C Y (C.cov X Z) W)) +
      (C.cov Z (curvature C X Y W) + (-1 : ℝ) • curvature C X Y (C.cov Z W) +
        (curvature C Z (C.cov X Y) W + (-1 : ℝ) • curvature C Z (C.cov Y X) W)) := by
      module
    _ = 0 := he

/-- The differential Bianchi identity as an endomorphism identity. -/
theorem second_bianchi : P202Specs.Geometry.SecondBianchi.second_bianchiType.{u} := by
  intro n a M _ S g C hC T hT p x y z
  apply LinearMap.ext; intro w
  obtain ⟨X, rfl⟩ := section_evaluation_surjective (tangentBundle S) p x
  obtain ⟨Y, rfl⟩ := section_evaluation_surjective (tangentBundle S) p y
  obtain ⟨Z, rfl⟩ := section_evaluation_surjective (tangentBundle S) p z
  obtain ⟨W, rfl⟩ := section_evaluation_surjective (tangentBundle S) p w
  change covariantDerivative C T p (X.val p) (Y.val p) (Z.val p) (W.val p) +
    covariantDerivative C T p (Y.val p) (Z.val p) (X.val p) (W.val p) +
    covariantDerivative C T p (Z.val p) (X.val p) (Y.val p) (W.val p) = 0
  rw [(derivative_rule C T p).1, (derivative_rule C T p).1, (derivative_rule C T p).1]
  have h := congrArg (fun V : Field S => V.val p) (field_second_bianchi C hC.1 T hT X Y Z W)
  simpa only [section_add_apply, section_zero_apply] using h

end P202.Geometry.SecondBianchi
