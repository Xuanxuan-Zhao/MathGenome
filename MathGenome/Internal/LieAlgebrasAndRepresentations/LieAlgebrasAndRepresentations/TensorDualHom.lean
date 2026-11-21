import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TensorDualHom

/-! Tensor, dual and Hom representations (LA-A06, source lines 414–459).
The actions are the canonical Mathlib ones. Evaluation and composition are
constructed on tensors and checked on pure tensors, then extended by
linearity. The canonical dual–tensor map is equivariant without any
finiteness assumption; finite dimension is used only for its inverse. -/

universe u v w w₁ w₂

namespace LieAlgebrasAndRepresentations.TensorDualHom
open scoped TensorProduct
open Specs.LieAlgebrasAndRepresentations.TensorDualHom

variable {k : Type u} [Field k]
variable {g : Type v} [LieRing g] [LieAlgebra k g]
variable {M : Type w} [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]
variable {N : Type w₁} [AddCommGroup N] [Module k N] [LieRingModule g N] [LieModule k g N]
variable {P : Type w₂} [AddCommGroup P] [Module k P] [LieRingModule g P] [LieModule k g P]

theorem actions_spec : actionsExpected.{u,v,w,w₁} := by
  intro k g _ _ _ M _ _ _ _ N _ _ _ _
  exact ⟨TensorProduct.LieModule.lie_tmul_right,
    fun x φ m => Module.Dual.lie_apply x m φ,
    fun x f m => LieHom.lie_apply f x m⟩

/-- Evaluation on the original Hom and module spaces is a Lie module map. -/
def evaluation : (M →ₗ[k] N) ⊗[k] M →ₗ⁅k,g⁆ N :=
  { evaluationLinear k M N with
    map_lie' := by
      intro x t
      change evaluationLinear k M N ⁅x, t⁆ = ⁅x, evaluationLinear k M N t⁆
      induction t using TensorProduct.inductionOn with
      | tmul f m =>
        simp only [TensorProduct.LieModule.lie_tmul_right, map_add,
          evaluationLinear, TensorProduct.lift.tmul, LinearMap.id_apply,
          LieHom.lie_apply]
        abel
      | add s t hs ht => simp only [lie_add, map_add, hs, ht] }

theorem evaluation_spec : evaluationExpected.{u,v,w,w₁} := by
  intro k g _ _ _ M _ _ _ _ N _ _ _ _
  exact ⟨evaluation (g := g), rfl⟩

/-- Composition is a Lie module map from the tensor product of Hom spaces. -/
def composition : (N →ₗ[k] P) ⊗[k] (M →ₗ[k] N) →ₗ⁅k,g⁆ (M →ₗ[k] P) :=
  { compositionLinear k M N P with
    map_lie' := by
      intro x t
      change compositionLinear k M N P ⁅x, t⁆ = ⁅x, compositionLinear k M N P t⁆
      induction t using TensorProduct.inductionOn with
      | tmul h f =>
        ext m
        simp only [TensorProduct.LieModule.lie_tmul_right, map_add,
          compositionLinear, TensorProduct.lift.tmul, LinearMap.llcomp_apply',
          LinearMap.add_apply, LinearMap.comp_apply, LieHom.lie_apply, map_sub]
        abel
      | add s t hs ht => simp only [lie_add, map_add, hs, ht] }

theorem composition_spec : compositionExpected.{u,v,w,w₁,w₂} := by
  intro k g _ _ _ M _ _ _ _ N _ _ _ _ P _ _ _ _
  exact ⟨composition (g := g), rfl⟩

/-- Scalar evaluation is invariant, i.e. equivariant for the trivial action on k. -/
theorem dual_evaluation_spec : dualEvaluationExpected.{u,v,w} := by
  intro k g _ _ _ M _ _ _ _ x t
  induction t using TensorProduct.inductionOn with
  | tmul φ m =>
    simp only [TensorProduct.LieModule.lie_tmul_right, map_add,
      dualEvaluationLinear, evaluationLinear, TensorProduct.lift.tmul,
      LinearMap.id_apply, Module.Dual.lie_apply, neg_add_cancel]
  | add s t hs ht =>
    change dualEvaluationLinear k M
      ((TensorProduct.LieModule.hasBracketAux (R := k) x) (s + t)) = 0
    rw [map_add, map_add]
    change dualEvaluationLinear k M ⁅x, s⁆ + dualEvaluationLinear k M ⁅x, t⁆ = 0
    rw [hs, ht, add_zero]

/-- The rank-one operator map φ ⊗ n ↦ (m ↦ φ(m)n) respects the actions. -/
def dualTensorHomMap : Module.Dual k M ⊗[k] N →ₗ⁅k,g⁆ (M →ₗ[k] N) :=
  { dualTensorHom k M N with
    map_lie' := by
      intro x t
      change dualTensorHom k M N ⁅x, t⁆ = ⁅x, dualTensorHom k M N t⁆
      induction t using TensorProduct.inductionOn with
      | tmul φ n =>
        ext m
        simp only [TensorProduct.LieModule.lie_tmul_right, map_add,
          LinearMap.add_apply, dualTensorHom_apply, Module.Dual.lie_apply,
          LieHom.lie_apply, lie_smul, neg_smul, sub_eq_add_neg]
        abel
      | add s t hs ht =>
        change dualTensorHom k M N
          ((TensorProduct.LieModule.hasBracketAux (R := k) x) (s + t)) = _
        rw [map_add, map_add]
        change dualTensorHom k M N ⁅x, s⁆ + dualTensorHom k M N ⁅x, t⁆ = _
        rw [hs, ht, map_add, lie_add] }

theorem dualTensorHom_spec : dualTensorHomExpected.{u,v,w,w₁} := by
  intro k g _ _ _ M _ _ _ _ N _ _ _ _
  exact ⟨dualTensorHomMap (g := g), rfl⟩

/-- Only the source module M must be finite dimensional; N is arbitrary. -/
noncomputable def finiteDualTensorHom [FiniteDimensional k M] :
    Module.Dual k M ⊗[k] N ≃ₗ⁅k,g⁆ (M →ₗ[k] N) :=
  { dualTensorHomEquiv k M N with
    map_lie' := (dualTensorHomMap (k := k) (g := g) (M := M) (N := N)).map_lie' }

theorem finiteDualTensorHom_spec : finiteDualTensorHomExpected.{u,v,w,w₁} := by
  intro k g _ _ _ M _ _ _ _ N _ _ _ _ _
  exact ⟨finiteDualTensorHom (g := g), rfl⟩

end LieAlgebrasAndRepresentations.TensorDualHom
