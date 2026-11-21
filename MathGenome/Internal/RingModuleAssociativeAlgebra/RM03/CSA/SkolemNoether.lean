import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Tensor
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SimpleArtinianModules

/-! Skolem–Noether for embeddings of a simple algebra into a central simple algebra. -/

namespace RM03.CSA

open scoped TensorProduct
open MulOpposite

universe u v w

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {B : Type w} [Ring B] [Algebra k B]

/-- Left multiplication by A and right multiplication through f. -/
private def embeddingAction (f : B →ₐ[k] A) : (A ⊗[k] Bᵐᵒᵖ) →ₐ[k] Module.End k A :=
  (AlgHom.mulLeftRight k A).comp (Algebra.TensorProduct.map (AlgHom.id k A) f.op)

private abbrev embeddingModule (f : B →ₐ[k] A) : Module (A ⊗[k] Bᵐᵒᵖ) A :=
  Module.compHom A (embeddingAction f).toRingHom

private theorem embeddingScalarTower (f : B →ₐ[k] A) :
    let := embeddingModule f
    IsScalarTower k (A ⊗[k] Bᵐᵒᵖ) A := by
  let := embeddingModule f
  refine IsScalarTower.of_algebraMap_smul (A := A ⊗[k] Bᵐᵒᵖ) fun c x ↦ ?_
  change embeddingAction f (algebraMap k (A ⊗[k] Bᵐᵒᵖ) c) x = c • x
  rw [(embeddingAction f).commutes c]
  rfl

private theorem embeddingAction_tmul (f : B →ₐ[k] A) (a : A) (b : B) (x : A) :
    embeddingAction f (a ⊗ₜ[k] op b) x = a * x * f b := by
  simp [embeddingAction]

/-- RM03-C04.07 in its intertwining form. -/
theorem skolem_noether (hA : IsCentralSimple k A) (hB : IsSimpleRing B)
    (f g : B →ₐ[k] A) (hf : Function.Injective f) (_hg : Function.Injective g) :
    ∃ u : Aˣ, ∀ b : B, f b * (u : A) = (u : A) * g b := by
  let : IsSimpleRing A := hA.1
  let : IsSimpleRing B := hB
  let : FiniteDimensional k A := hA.2.2
  let : FiniteDimensional k B := FiniteDimensional.of_injective f.toLinearMap hf
  let : FiniteDimensional k Bᵐᵒᵖ := Module.Finite.equiv (opLinearEquiv k : B ≃ₗ[k] Bᵐᵒᵖ)
  let T := A ⊗[k] Bᵐᵒᵖ
  let : IsSimpleRing T := isSimpleRing_tensor hA inferInstance
  -- Pass both actions explicitly, since they are on the same underlying type.
  obtain ⟨F⟩ := @SimpleArtinianModules.equivOfFinrankEq k T _ _ _ _ _
    A _ _ (embeddingModule f) (embeddingScalarTower f) _ _
    A _ _ (embeddingModule g) (embeddingScalarTower g) _ _ rfl
  have hF (x : A) : F x = x * F 1 := by
    let z := x ⊗ₜ[k] op (1 : B)
    have h := F.map_smul z 1
    change F (embeddingAction f z 1) = embeddingAction g z (F 1) at h
    simpa only [z, embeddingAction_tmul, map_one, mul_one] using h
  have hInv (x : A) : F.symm x = x * F.symm 1 := by
    let z := x ⊗ₜ[k] op (1 : B)
    have h := F.symm.map_smul z 1
    change F.symm (embeddingAction g z 1) = embeddingAction f z (F.symm 1) at h
    simpa only [z, embeddingAction_tmul, map_one, mul_one] using h
  let u : Aˣ :=
    ⟨F 1, F.symm 1, (hInv (F 1)).symm.trans (F.symm_apply_apply 1),
      (hF (F.symm 1)).symm.trans (F.apply_symm_apply 1)⟩
  refine ⟨u, fun b ↦ ?_⟩
  have hb : F (f b) = F 1 * g b := by
    let z := (1 : A) ⊗ₜ[k] op b
    have h := F.map_smul z 1
    change F (embeddingAction f z 1) = embeddingAction g z (F 1) at h
    simpa only [z, embeddingAction_tmul, one_mul] using h
  exact (hF (f b)).symm.trans hb

/-- Two embeddings of a simple algebra into a central simple algebra are conjugate. -/
theorem skolem_noether_conj (hA : IsCentralSimple k A) (hB : IsSimpleRing B)
    (f g : B →ₐ[k] A) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ u : Aˣ, ∀ b : B, g b = (↑u⁻¹ : A) * f b * (u : A) := by
  obtain ⟨u, hu⟩ := skolem_noether hA hB f g hf hg
  refine ⟨u, fun b ↦ ?_⟩
  calc
    g b = (↑u⁻¹ : A) * ((u : A) * g b) := (u.inv_mul_cancel_left _).symm
    _ = (↑u⁻¹ : A) * f b * (u : A) := by rw [← hu b, mul_assoc]

/-- In particular, every algebra automorphism of a central simple algebra is inner. -/
theorem algEquiv_isInner (hA : IsCentralSimple k A) (e : A ≃ₐ[k] A) :
    ∃ u : Aˣ, ∀ a : A, e a = (u : A) * a * (↑u⁻¹ : A) := by
  obtain ⟨u, hu⟩ := skolem_noether hA hA.1 e.toAlgHom (AlgHom.id k A) e.injective
    Function.injective_id
  refine ⟨u, fun a ↦ ?_⟩
  have ha : e a * (u : A) = (u : A) * a := hu a
  rw [← ha, mul_assoc, Units.mul_inv, mul_one]

end RM03.CSA
