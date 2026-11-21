import MathGenome.Internal.Specs.D07.Ch04.SemidirectProduct
import MathGenome.Internal.D07.Ch01.AutomorphismGroups
import MathGenome.Internal.D07.Ch04.DirectProducts

/-!
External semidirect products (`K07.04.semidirect_product`).
We use the canonical two-coordinate construction with the source's left
conjugation convention. The first range is the kernel of projection to H.
Complementarity follows from the unique coordinate factorization.
-/

namespace D07.Ch04.SemidirectProduct

universe u v

abbrev Product (N : Type u) (H : Type v) [Group N] [Group H]
    (φ : H →* MulAut N) : Type (max u v) := _root_.SemidirectProduct N H φ

abbrev productGroup (N : Type u) (H : Type v) [Group N] [Group H]
    (φ : H →* MulAut N) : Group (Product N H φ) := inferInstance

def coordinates (N : Type u) (H : Type v) [Group N] [Group H]
    (φ : H →* MulAut N) : Product N H φ ≃ N × H :=
  _root_.SemidirectProduct.equivProd

def inclusionN (N : Type u) (H : Type v) [Group N] [Group H]
    (φ : H →* MulAut N) : N →* Product N H φ := _root_.SemidirectProduct.inl

def inclusionH (N : Type u) (H : Type v) [Group N] [Group H]
    (φ : H →* MulAut N) : H →* Product N H φ := _root_.SemidirectProduct.inr

def projection (N : Type u) (H : Type v) [Group N] [Group H]
    (φ : H →* MulAut N) : Product N H φ →* H := _root_.SemidirectProduct.rightHom

theorem operations : Specs.D07.Ch04.SemidirectProduct.Operations.{u, v} := by
  intro N H _ _ φ
  exact ⟨fun _ _ => rfl, rfl, fun _ => rfl⟩

theorem group_laws : Specs.D07.Ch04.SemidirectProduct.GroupLaws.{u, v} := by
  intro N H _ _ φ
  exact D07.Ch01.GroupDefinition.group_laws (Product N H φ)

theorem embeddings : Specs.D07.Ch04.SemidirectProduct.Embeddings.{u, v} := by
  intro N H _ _ φ
  exact ⟨fun _ => rfl, fun _ => rfl,
    _root_.SemidirectProduct.inl_injective, _root_.SemidirectProduct.inr_injective⟩

theorem projection_laws : Specs.D07.Ch04.SemidirectProduct.ProjectionLaws.{u, v} := by
  intro N H _ _ φ
  exact ⟨fun _ => rfl, _root_.SemidirectProduct.rightHom_surjective,
    _root_.SemidirectProduct.range_inl_eq_ker_rightHom.symm⟩

theorem first_factor_normal : Specs.D07.Ch04.SemidirectProduct.FirstFactorNormal.{u, v} := by
  intro N H _ _ φ
  rw [← (projection_laws N H φ).2.2]
  exact D07.Ch01.KernelImage.kernel_normal (Product N H φ) H (projection N H φ)

theorem factorization : Specs.D07.Ch04.SemidirectProduct.Factorization.{u, v} := by
  intro N H _ _ φ x
  exact (_root_.SemidirectProduct.inl_left_mul_inr_right x).symm

theorem second_factor_complement :
    Specs.D07.Ch04.SemidirectProduct.SecondFactorComplement.{u, v} := by
  intro N H _ _ φ
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro x hxN hxH
    rcases hxN with ⟨n, rfl⟩
    rcases hxH with ⟨h, heq⟩
    have hn : n = 1 := (congrArg _root_.SemidirectProduct.left heq).symm
    subst n
    exact map_one _
  · apply Set.eq_univ_of_forall
    intro x
    exact ⟨_root_.SemidirectProduct.inl x.left, ⟨x.left, rfl⟩,
      _root_.SemidirectProduct.inr x.right, ⟨x.right, rfl⟩,
      _root_.SemidirectProduct.inl_left_mul_inr_right x⟩

theorem factors_intersect_trivially :
    Specs.D07.Ch04.SemidirectProduct.FactorsIntersectTrivially.{u, v} := by
  intro N H _ _ φ
  exact (second_factor_complement N H φ).disjoint.eq_bot

theorem trivial_action_multiplication :
    Specs.D07.Ch04.SemidirectProduct.TrivialActionMultiplication.{u, v} := by
  intro N H _ _ φ hφ x y
  change (x.left * φ x.right y.left, x.right * y.right) =
    (x.left * y.left, x.right * y.right)
  rw [hφ, MulAut.one_apply]

theorem trivial_action_iso : Specs.D07.Ch04.SemidirectProduct.TrivialActionIso.{u, v} := by
  intro N H _ _ φ hφ
  refine ⟨{ _root_.SemidirectProduct.equivProd with
    map_mul' := trivial_action_multiplication N H φ hφ }, fun _ => rfl⟩

end D07.Ch04.SemidirectProduct
