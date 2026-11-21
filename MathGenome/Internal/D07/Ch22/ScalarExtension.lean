import MathGenome.Internal.Specs.D07.Ch22.ScalarExtension
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.TensorProduct.Finite

/-! K07.22.scalar_extension. The canonical tensor action descends the
balanced relations. The Hom equivalence is evaluation at `1 ⊗ m` and its
inverse is the tower-aware linear lift. Bases use finite-support coordinates.
The torsion argument uses a nonzero integer annihilator separately for each
vector, so it also applies to infinite torsion groups. -/

noncomputable section
universe u v w t
namespace D07.Ch22.ScalarExtension
open Specs.D07.Ch22.ScalarExtension
open scoped TensorProduct

theorem ringHomAction : RingHomAction.{u, v, w} := by
  intro R _ S _ φ M _ _
  let : Algebra R S := φ.toAlgebra
  exact ⟨⟨one_smul S, mul_smul, add_smul, smul_add⟩, fun _ _ _ => rfl⟩

theorem restrictionOfScalars : RestrictionOfScalars.{u, v, t} := by
  intro R _ S _ φ N _ _
  exact ⟨Module.compHom N φ, fun _ _ => rfl⟩

theorem naturalMap : NaturalMap.{u, v, w} := by
  intro R _ S _ _ M _ _
  exact ⟨TensorProduct.mk R S M 1, fun _ => rfl⟩

theorem liftBalanced : LiftBalanced.{u, v, w, t} := by
  intro R _ S _ _ M _ _ N _ _ _ _ h
  refine ⟨?_, ?_, ?_⟩
  · intro s s' m
    exact add_smul s s' (h m)
  · intro s m m'
    rw [h.map_add, smul_add]
  · intro r s m
    rw [h.map_smul, smul_assoc, smul_comm]

theorem homEquivalence : HomEquivalence.{u, v, w, t} := by
  intro R _ S _ _ M _ _ N _ _ _ _
  exact ⟨(LinearMap.liftBaseChangeEquiv S).symm,
    fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ringHomHomEquivalence : RingHomHomEquivalence.{u, v, w, t} := by
  intro R _ S _ φ M _ _ N _ _
  let : Algebra R S := φ.toAlgebra
  let : Module R N := Module.compHom N φ
  let : IsScalarTower R S N :=
    { smul_assoc := fun r s n => mul_smul (φ r) s n }
  exact homEquivalence R S M N

theorem universalProperty : UniversalProperty.{u, v, w, t} := by
  intro R _ S _ _ M _ _ N _ _ _ _ h
  refine ⟨h.liftBaseChange S, fun _ _ => rfl, ?_⟩
  intro G hG
  apply (LinearMap.liftBaseChangeEquiv S).symm.injective
  ext m
  simpa using hG 1 m

theorem torsionTensor : TorsionTensor.{w} := by
  intro M _ q m d hd hm
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have h : q ⊗ₜ[ℤ] m = (q / (d : ℚ)) ⊗ₜ[ℤ] (d • m) := by
    rw [← TensorProduct.smul_tmul]
    congr 1
    simp only [zsmul_eq_mul]
    exact (mul_div_cancel₀ q hdq).symm
  exact ⟨h, by rw [h, hm, TensorProduct.tmul_zero]⟩

theorem torsionVanishing : TorsionVanishing.{w} := by
  intro M _ h x
  induction x using TensorProduct.inductionOn with
  | tmul q m =>
    obtain ⟨d, hd, hm⟩ := h m
    exact (torsionTensor M q m d hd hm).2
  | add x y hx hy => rw [hx, hy, add_zero]

theorem finiteVanishing : FiniteVanishing.{w} := by
  intro M _ _ x
  apply torsionVanishing M _ x
  intro m
  refine ⟨(addOrderOf m : ℤ), ?_, ?_⟩
  · exact_mod_cast (isOfFinAddOrder_of_finite m).addOrderOf_pos.ne'
  · simp

theorem noninjectiveExample : NoninjectiveExample := by
  intro h
  have he : (1 : ZMod 2) = 0 := h
    ((finiteVanishing (ZMod 2) ((1 : ℚ) ⊗ₜ[ℤ] (1 : ZMod 2))).trans
      (finiteVanishing (ZMod 2) ((1 : ℚ) ⊗ₜ[ℤ] (0 : ZMod 2))).symm)
  exact one_ne_zero he

theorem fieldBasis : FieldBasis.{u, v, w, t} := by
  intro F _ L _ _ M _ _ ι b
  refine ⟨b.baseChange L, (fun i => b.baseChange_apply L i), ?_⟩
  intro s m i
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]

theorem fieldCoordinates : FieldCoordinates.{u, v, w, t} := by
  intro F _ L _ _ M _ _ ι b
  refine ⟨(b.baseChange L).repr, ?_, ?_⟩
  · intro m i
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  · intro i
    rw [Module.Basis.repr_symm_single, one_smul, Module.Basis.baseChange_apply]

theorem fieldInjectivity : FieldInjectivity.{u, v, w} := by
  intro F _ L _ _ M _ _ x y hxy
  let b := Module.Free.chooseBasis F M
  apply b.repr.injective
  ext i
  apply (algebraMap F L).injective
  have h := congrArg (fun z => (b.baseChange L).repr z i) hxy
  simpa only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one] using h

theorem finiteDimension : FiniteDimension.{u, v, w} := by
  intro F _ L _ _ M _ _ _
  exact ⟨inferInstance, Module.finrank_baseChange⟩

end D07.Ch22.ScalarExtension
