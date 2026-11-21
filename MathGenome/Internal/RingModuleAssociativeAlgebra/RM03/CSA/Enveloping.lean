import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Defs
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Density.FiniteQuotient
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.TensorProduct.Finite

/-! The enveloping algebra of a central simple algebra, via finite Jacobson density. -/

namespace RM03.CSA

open scoped TensorProduct
open MulOpposite

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

attribute [local instance] instModuleTensorProductMop

private theorem tensor_smul_eq (z : A ⊗[k] Aᵐᵒᵖ) (x : A) :
    z • x = AlgHom.mulLeftRight k A z x :=
  rfl

private theorem tmul_smul_eq (a b x : A) : (a ⊗ₜ[k] op b) • x = a * x * b := by
  rw [tensor_smul_eq, AlgHom.mulLeftRight_apply, unop_op]

private theorem enveloping_isScalarTower : IsScalarTower k (A ⊗[k] Aᵐᵒᵖ) A :=
  IsScalarTower.of_algebraMap_smul fun c x ↦ by
    change AlgHom.mulLeftRight k A (algebraMap k (A ⊗[k] Aᵐᵒᵖ) c) x = c • x
    rw [(AlgHom.mulLeftRight k A).commutes c]
    rfl

attribute [local instance] enveloping_isScalarTower

/-- A tensor-action submodule is closed under both left and right multiplication. -/
private def toTwoSidedIdeal (S : Submodule (A ⊗[k] Aᵐᵒᵖ) A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (S : Set A) S.zero_mem S.add_mem S.neg_mem
    (fun {x y} hy ↦ by
      change x * y ∈ S
      simpa only [tmul_smul_eq, mul_one] using S.smul_mem (x ⊗ₜ[k] op (1 : A)) hy)
    (fun {x y} hx ↦ by
      change x * y ∈ S
      simpa only [tmul_smul_eq, one_mul] using S.smul_mem ((1 : A) ⊗ₜ[k] op y) hx)

/-- A two-sided ideal is stable under the tensor action by linearity in the tensor. -/
private def toEnvelopingSubmodule (I : TwoSidedIdeal A) : Submodule (A ⊗[k] Aᵐᵒᵖ) A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' z x hx := by
    change z • x ∈ I
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        rw [← op_unop b, tmul_smul_eq]
        exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)
    | add z w hz hw => simpa only [add_smul] using I.add_mem hz hw

private def envelopingSubmoduleOrderIso :
    TwoSidedIdeal A ≃o Submodule (A ⊗[k] Aᵐᵒᵖ) A where
  toFun := toEnvelopingSubmodule
  invFun := toTwoSidedIdeal
  left_inv _ := TwoSidedIdeal.ext fun _ ↦ by
    simp [toTwoSidedIdeal, toEnvelopingSubmodule]
  right_inv S := Submodule.ext fun x ↦ by
    change x ∈ toTwoSidedIdeal S ↔ x ∈ S
    simp [toTwoSidedIdeal]
  map_rel_iff' := Iff.rfl

private theorem enveloping_simple [IsSimpleRing A] :
    IsSimpleModule (A ⊗[k] Aᵐᵒᵖ) A :=
  (isSimpleModule_iff _ _).mpr
    ((envelopingSubmoduleOrderIso (k := k) (A := A)).isSimpleOrder_iff.mp inferInstance)

/-- The bimodule endomorphisms are precisely the scalar maps. -/
private theorem enveloping_end_scalars_surjective [Algebra.IsCentral k A] :
    Function.Surjective (algebraMap k (Module.End (A ⊗[k] Aᵐᵒᵖ) A)) := by
  intro f
  have left (x : A) : f x = x * f 1 := by
    simpa only [tmul_smul_eq, mul_one] using f.map_smul (x ⊗ₜ[k] op (1 : A)) 1
  have right (x : A) : f x = f 1 * x := by
    simpa only [tmul_smul_eq, one_mul] using f.map_smul ((1 : A) ⊗ₜ[k] op x) 1
  have hcenter : f 1 ∈ Subalgebra.center k A :=
    Subalgebra.mem_center_iff.mpr fun x ↦ (left x).symm.trans (right x)
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hcenter)
  refine ⟨c, LinearMap.ext fun x ↦ ?_⟩
  rw [Module.algebraMap_end_apply, right, ← hc, Algebra.smul_def]

/-- Finite Jacobson density makes the tensor action surjective onto all base-field-linear maps. -/
private theorem mulLeftRight_surjective (h : IsCentralSimple k A) :
    Function.Surjective (AlgHom.mulLeftRight k A) := by
  let : IsSimpleRing A := h.1
  let : Algebra.IsCentral k A := h.2.1
  let : FiniteDimensional k A := h.2.2
  let : IsSimpleModule (A ⊗[k] Aᵐᵒᵖ) A := enveloping_simple
  let : Module.Finite (Module.End (A ⊗[k] Aᵐᵒᵖ) A) A :=
    Module.Finite.of_restrictScalars_finite k (Module.End (A ⊗[k] Aᵐᵒᵖ) A) A
  intro T
  let F : Density.RightEnd (A ⊗[k] Aᵐᵒᵖ) A :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f x ↦ by
        obtain ⟨c, rfl⟩ := enveloping_end_scalars_surjective f
        simpa only [Module.End.smul_def, Module.algebraMap_end_apply, RingHom.id_apply]
          using T.map_smul c x }
  obtain ⟨z, hz⟩ := Density.action_surjective_of_finite (A ⊗[k] Aᵐᵒᵖ) A F
  exact ⟨z, LinearMap.ext fun x ↦ DFunLike.congr_fun hz x⟩

/-- Left and right multiplication identifies the enveloping algebra with the full endomorphism ring. -/
theorem mulLeftRight_bijective (h : IsCentralSimple k A) :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  let : FiniteDimensional k A := h.2.2
  have hsurj := mulLeftRight_surjective h
  have hdim : Module.finrank k (A ⊗[k] Aᵐᵒᵖ) = Module.finrank k (Module.End k A) := by
    rw [Module.finrank_tensorProduct, ← (opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).finrank_eq]
    exact (Module.finrank_linearMap k k A A).symm
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (AlgHom.mulLeftRight k A).toLinearMap)).mpr hsurj, hsurj⟩

/-- RM03-C04.03, with its forward algebra homomorphism fixed. -/
theorem enveloping_isomorphism (h : IsCentralSimple k A) :
    ∃ e : (A ⊗[k] Aᵐᵒᵖ) ≃ₐ[k] Module.End k A, e.toAlgHom = AlgHom.mulLeftRight k A :=
  ⟨AlgEquiv.ofBijective (AlgHom.mulLeftRight k A) (mulLeftRight_bijective h), rfl⟩

end RM03.CSA
