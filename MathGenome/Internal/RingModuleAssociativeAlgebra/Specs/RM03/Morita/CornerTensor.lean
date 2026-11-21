import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.Corner
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.MoritaEvaluations
import Mathlib.CategoryTheory.NatIso

/-! The dual and balanced tensor for the corner of an arbitrary idempotent. -/

universe u v w s

namespace RM03.Morita

open MulOpposite CategoryTheory
open P103.BalancedTensor (Tensor tmul)

variable {R : Type u} [Ring R]

/-- The right R-linear dual of eR, using the regular right module R. -/
abbrev CornerDual (e : Idempotent R) := P103.Morita.Q R (rightIdeal e)

/-- The right corner action on the dual is precomposition with left multiplication. -/
instance cornerDualRightModule (e : Idempotent R) : Module (Corner e)ᵐᵒᵖ (CornerDual e) :=
  Module.compHom (CornerDual e) (RingHom.op (cornerToEnd e))

@[simp] theorem cornerDual_right_apply (e : Idempotent R)
    (a : (Corner e)ᵐᵒᵖ) (f : CornerDual e) (x : rightIdeal e) :
    (a • f) x = f (a.unop • x) := rfl

@[simp] theorem cornerDual_left_apply (e : Idempotent R)
    (r : R) (f : CornerDual e) (x : rightIdeal e) :
    (r • f) x = r * f x := rfl

instance cornerDualBimodule (e : Idempotent R) :
    SMulCommClass (Corner e)ᵐᵒᵖ R (CornerDual e) where
  smul_comm _ _ _ := LinearMap.ext fun _ => rfl

/-- Tensor on the right with a bimodule. The target scalars act through the
second tensor factor. For right output modules take S to be an opposite ring. -/
def tensorWithBimodule {S : Type s} [Ring S] (B : Type w) [AddCommGroup B]
    [Module R B] [Module S B] [SMulCommClass S R B] :
    ModuleCat.{max v w} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} S :=
  letI (M : ModuleCat.{max v w} Rᵐᵒᵖ) : Module S (Tensor R M B) :=
    P103.BalancedTensor.rightModule
  { obj M := ModuleCat.of S (Tensor R M B)
    map f := ModuleCat.ofHom
      (P103.BalancedTensor.mapRightLinear f.hom (LinearMap.id (R := R) (M := B))
        (S := S) (fun _ _ => rfl))
    map_id M := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change P103.BalancedTensor.map LinearMap.id LinearMap.id z = z
      rw [P103.BalancedTensor.map_id]
      rfl
    map_comp f g := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      let i : B →ₗ[R] B := LinearMap.id
      change P103.BalancedTensor.map (g.hom.comp f.hom) (i.comp i) z =
        (P103.BalancedTensor.map g.hom i).comp (P103.BalancedTensor.map f.hom i) z
      rw [P103.BalancedTensor.map_comp] }

@[simp] theorem tensorWithBimodule_map_tmul {S : Type s} [Ring S]
    (B : Type w) [AddCommGroup B] [Module R B] [Module S B] [SMulCommClass S R B]
    {M N : ModuleCat.{max v w} Rᵐᵒᵖ} (f : M ⟶ N) (m : M) (b : B) :
    (tensorWithBimodule (S := S) B).map f (tmul R m b) = tmul R (f m) b := rfl

section
variable (e : Idempotent R) (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The right corner-module structure of M ⊗[R] Re. -/
instance cornerTensorModule : Module (Corner e)ᵐᵒᵖ (Tensor R M (leftIdeal e)) :=
  P103.BalancedTensor.rightModule

@[simp] theorem cornerTensor_smul_tmul (a : (Corner e)ᵐᵒᵖ) (m : M) (b : leftIdeal e) :
    a • tmul R m b = tmul R m (a • b) := rfl

end

/-- The functor M ↦ M ⊗[R] Re on right modules. The category universe
accommodates both the modules and the tensor factor Re. -/
abbrev cornerTensorFunctor (e : Idempotent R) :
    ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v} (Corner e)ᵐᵒᵖ :=
  tensorWithBimodule (leftIdeal e)

/-- Tensoring with the right-linear dual, with scalars restricted to the corner
by its canonical map to the endomorphism ring of eR. -/
abbrev cornerDualTensorFunctor (e : Idempotent R) :
    ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v} (Corner e)ᵐᵒᵖ :=
  tensorWithBimodule (CornerDual e)

namespace CornerTensorSpec

/-- Evaluation at e, with the inverse and both scalar actions specified. -/
def dualEquivType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    ∃ E : CornerDual e ≃ₗ[R] leftIdeal e,
      (∀ f, (E f).val = f (rightGenerator e)) ∧
      (∀ (b : leftIdeal e) (x : rightIdeal e), E.symm b x = b.val * x.val) ∧
      (∀ (a : (Corner e)ᵐᵒᵖ) f, E (a • f) = a • E f)

/-- The right eRe-linear tensor comparison for modules in any universe. -/
def tensorEquivType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R) (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M],
    ∃ E : Tensor R M (leftIdeal e) ≃ₗ[(Corner e)ᵐᵒᵖ] moduleCorner (M := M) e,
      (∀ (m : M) (b : leftIdeal e), (E (tmul R m b)).val = op b.val • m) ∧
      (∀ x, E.symm x = tmul R x.val (leftGenerator e))

/-- The tensor comparison is natural for the existing corner functor. -/
def tensorIsoType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    ∃ η : cornerTensorFunctor.{u,v} e ≅ CornerSpec.cornerFunctorValue e,
      (∀ (M : ModuleCat.{max u v} Rᵐᵒᵖ) (m : M) (b : leftIdeal e),
        ((η.hom.app M) (tmul R m b)).val = op b.val • m) ∧
      (∀ (M : ModuleCat.{max u v} Rᵐᵒᵖ) (x : moduleCorner (M := M) e),
        (η.inv.app M) x = tmul R x.val (leftGenerator e))

/-- Evaluation on the dual induces the identification of the two tensor functors. -/
def dualTensorIsoType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    ∃ η : cornerDualTensorFunctor.{u,v} e ≅ cornerTensorFunctor e,
      ∀ (M : ModuleCat.{max u v} Rᵐᵒᵖ) (m : M) (f : CornerDual e),
        ∃ b : leftIdeal e, b.val = f (rightGenerator e) ∧
          (η.hom.app M) (tmul R m f) = tmul R m b

end CornerTensorSpec
end RM03.Morita
