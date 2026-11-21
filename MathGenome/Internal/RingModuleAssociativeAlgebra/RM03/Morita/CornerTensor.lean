import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.CornerTensor
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Morita.Corner

/-! Evaluation on eR and multiplication on the balanced tensor with Re. -/

universe u v w

namespace RM03.Morita

open MulOpposite CategoryTheory
open P103.BalancedTensor (Tensor tmul)

variable {R : Type u} [Ring R]

private def dualEvaluation (e : Idempotent R) : CornerDual e →ₗ[R] leftIdeal e where
  toFun f := ⟨f (rightGenerator e), by
    have he : op e.val • rightGenerator e = rightGenerator e := Subtype.ext e.property
    have hf := f.map_smul (op e.val) (rightGenerator e)
    rw [he] at hf
    exact hf.symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def dualFromLeftIdeal (e : Idempotent R) (b : leftIdeal e) : CornerDual e where
  toFun x := b.val * x.val
  map_add' x y := mul_add b.val x.val y.val
  map_smul' r x := (mul_assoc b.val x.val r.unop).symm

/-- A right R-linear functional on eR is determined by its value at e. -/
def cornerDualEquiv (e : Idempotent R) : CornerDual e ≃ₗ[R] leftIdeal e where
  __ := dualEvaluation e
  invFun := dualFromLeftIdeal e
  left_inv f := LinearMap.ext fun x => by
    have hx : op x.val • rightGenerator e = x := Subtype.ext x.property
    have hf := f.map_smul (op x.val) (rightGenerator e)
    rw [hx] at hf
    exact hf.symm
  right_inv b := Subtype.ext b.property

@[simp] theorem cornerDualEquiv_apply_val (e : Idempotent R) (f : CornerDual e) :
    (cornerDualEquiv e f).val = f (rightGenerator e) := rfl

@[simp] theorem cornerDualEquiv_symm_apply (e : Idempotent R) (b : leftIdeal e)
    (x : rightIdeal e) : (cornerDualEquiv e).symm b x = b.val * x.val := rfl

@[simp] theorem cornerDualEquiv_right_smul (e : Idempotent R)
    (a : (Corner e)ᵐᵒᵖ) (f : CornerDual e) :
    cornerDualEquiv e (a • f) = a • cornerDualEquiv e f := by
  apply Subtype.ext
  change f (a.unop • rightGenerator e) = f (rightGenerator e) * a.unop.val
  have h : a.unop • rightGenerator e = op a.unop.val • rightGenerator e :=
    Subtype.ext (a.unop.property.2.trans a.unop.property.1.symm)
  rw [h]
  exact f.map_smul _ _

theorem corner_dual : CornerTensorSpec.dualEquivType.{u} :=
  fun e => ⟨cornerDualEquiv e, cornerDualEquiv_apply_val e, cornerDualEquiv_symm_apply e,
    cornerDualEquiv_right_smul e⟩

section TensorComparison

variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

private def multiplyPairing (e : Idempotent R) :
    P103.BalancedTensor.Pairing R (A := M) (B := leftIdeal e) (moduleCorner (M := M) e) :=
  P103.BalancedTensor.Pairing.ofFun
    (fun m b => ⟨op b.val • m, by
      change op e.val • (op b.val • m) = op b.val • m
      rw [← mul_smul, ← op_mul, b.property]⟩)
    (fun m n b => Subtype.ext (smul_add (op b.val) m n))
    (fun m b c => Subtype.ext (add_smul (op b.val) (op c.val) m))
    (fun r m b => Subtype.ext (mul_smul (op b.val) (op r) m).symm)

private def tensorToCorner (e : Idempotent R) :
    Tensor R M (leftIdeal e) →ₗ[(Corner e)ᵐᵒᵖ] moduleCorner (M := M) e where
  __ := P103.BalancedTensor.lift (multiplyPairing e)
  map_smul' a z :=
    P103.BalancedTensor.lift_rightScale (multiplyPairing e)
      (fun c m b => Subtype.ext (mul_smul (op c.unop.val) (op b.val) m)) a z

private def cornerToTensorAdd (e : Idempotent R) :
    moduleCorner (M := M) e →+ Tensor R M (leftIdeal e) :=
  (P103.BalancedTensor.pairing.toBiadditive.flip (leftGenerator e)).comp
    (moduleCorner (M := M) e).subtype

/-- Multiplication identifies M ⊗[R] Re with Me. -/
def cornerTensorEquiv (e : Idempotent R) :
    Tensor R M (leftIdeal e) ≃ₗ[(Corner e)ᵐᵒᵖ] moduleCorner (M := M) e where
  __ := tensorToCorner e
  invFun := cornerToTensorAdd e
  left_inv z := by
    change cornerToTensorAdd e (tensorToCorner e z) = z
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht m b =>
      change tmul R (op b.val • m) (leftGenerator e) = tmul R m b
      have hb : b.val • leftGenerator e = b := Subtype.ext b.property
      rw [P103.BalancedTensor.balance, hb]
    | ha z z' hz hz' => simp [hz, hz']
  right_inv x := Subtype.ext x.property

@[simp] theorem cornerTensorEquiv_tmul_val (e : Idempotent R) (m : M) (b : leftIdeal e) :
    (cornerTensorEquiv e (tmul R m b)).val = op b.val • m := rfl

@[simp] theorem cornerTensorEquiv_symm_apply (e : Idempotent R)
    (x : moduleCorner (M := M) e) :
    (cornerTensorEquiv e).symm x = tmul R x.val (leftGenerator e) := rfl

theorem cornerTensorEquiv_natural {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]
    (e : Idempotent R) (f : M →ₗ[Rᵐᵒᵖ] N) (z : Tensor R M (leftIdeal e)) :
    cornerTensorEquiv e (P103.BalancedTensor.map f LinearMap.id z) =
      restrictToCorner e f (cornerTensorEquiv e z) := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht m b =>
    apply Subtype.ext
    change op b.val • f m = f (op b.val • m)
    exact (f.map_smul (op b.val) m).symm
  | ha z z' hz hz' => simp [hz, hz']

end TensorComparison

theorem corner_tensor : CornerTensorSpec.tensorEquivType.{u,v} :=
  fun e _ _ _ => ⟨cornerTensorEquiv e, cornerTensorEquiv_tmul_val e,
    cornerTensorEquiv_symm_apply e⟩

/-- The multiplication comparison as a natural isomorphism of right-module functors. -/
def cornerTensorIso (e : Idempotent R) : cornerTensorFunctor.{u,v} e ≅ cornerFunctor e :=
  NatIso.ofComponents (fun M => (cornerTensorEquiv (M := M) e).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact cornerTensorEquiv_natural e f.hom)

theorem corner_tensor_natural : CornerTensorSpec.tensorIsoType.{u,v} :=
  fun e => ⟨cornerTensorIso e, fun _ _ _ => rfl, fun _ _ => rfl⟩

private def cornerDualTensorEquiv (e : Idempotent R)
    (M : ModuleCat.{max u v} Rᵐᵒᵖ) :
    (cornerDualTensorFunctor e).obj M ≃ₗ[(Corner e)ᵐᵒᵖ] (cornerTensorFunctor e).obj M := by
  let E := cornerDualEquiv e
  let i : M →ₗ[Rᵐᵒᵖ] M := LinearMap.id
  have hSymm (a : (Corner e)ᵐᵒᵖ) (b : leftIdeal e) : E.symm (a • b) = a • E.symm b := by
    apply E.injective
    rw [E.apply_symm_apply, cornerDualEquiv_right_smul, E.apply_symm_apply]
  let F := P103.BalancedTensor.mapRightLinear i E.toLinearMap (cornerDualEquiv_right_smul e)
  let G := P103.BalancedTensor.mapRightLinear i E.symm.toLinearMap hSymm
  refine LinearEquiv.ofLinearMap F G (LinearMap.ext fun z => ?_) (LinearMap.ext fun z => ?_)
  · change ((P103.BalancedTensor.map i E.toLinearMap).comp
      (P103.BalancedTensor.map i E.symm.toLinearMap)) z = z
    rw [← P103.BalancedTensor.map_comp, LinearEquiv.comp_symm]
    exact DFunLike.congr_fun (P103.BalancedTensor.map_id (R := R) (A := M)
      (B := leftIdeal e)) z
  · change ((P103.BalancedTensor.map i E.symm.toLinearMap).comp
      (P103.BalancedTensor.map i E.toLinearMap)) z = z
    rw [← P103.BalancedTensor.map_comp, LinearEquiv.symm_comp]
    exact DFunLike.congr_fun (P103.BalancedTensor.map_id (R := R) (A := M)
      (B := CornerDual e)) z

/-- Tensoring evaluation at e identifies the dual tensor functor with
tensoring by Re. -/
def cornerDualTensorIso (e : Idempotent R) :
    cornerDualTensorFunctor.{u,v} e ≅ cornerTensorFunctor e :=
  NatIso.ofComponents (fun M => (cornerDualTensorEquiv e M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let E := (cornerDualEquiv e).toLinearMap
    let i : leftIdeal e →ₗ[R] leftIdeal e := LinearMap.id
    let j : CornerDual e →ₗ[R] CornerDual e := LinearMap.id
    change ((P103.BalancedTensor.map LinearMap.id E).comp
        (P103.BalancedTensor.map f.hom j)) z =
      ((P103.BalancedTensor.map f.hom i).comp
        (P103.BalancedTensor.map LinearMap.id E)) z
    rw [← P103.BalancedTensor.map_comp, ← P103.BalancedTensor.map_comp,
      LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id])

theorem corner_dual_tensor_natural : CornerTensorSpec.dualTensorIsoType.{u,v} :=
  fun e => ⟨cornerDualTensorIso e, fun _ _ f => ⟨cornerDualEquiv e f, rfl, rfl⟩⟩

end RM03.Morita
