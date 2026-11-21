import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.FullEquivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Morita.Corner
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Morita.FullGenerator

/-! Multiplication and the explicit equivalence for a full corner. -/

universe u v

namespace RM03.Morita

open CategoryTheory MulOpposite
open P103.BalancedTensor

variable {R : Type u} [Ring R]

/-- Right multiplication by e sends eR to eRe. -/
private def projectToCorner (e : Idempotent R) (x : rightIdeal e) : Corner e :=
  ⟨x.val * e.val, by rw [← mul_assoc, x.property], by rw [mul_assoc, e.property.eq]⟩

@[instance_reducible] local instance rightIdealTensorModule
    (e : Idempotent R) (N : Type*) [AddCommGroup N] [Module (Corner e)ᵐᵒᵖ N] :
    Module Rᵐᵒᵖ (Tensor (Corner e) N (rightIdeal e)) := rightModule

private def multiplicationPairing (e : Idempotent R)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Pairing (Corner e) (A := moduleCorner (M := M) e) (B := rightIdeal e) M :=
  Pairing.ofFun (fun m x => op x.val • m.val)
    (fun m n x => smul_add (op x.val) m.val n.val)
    (fun m x y => add_smul (op x.val) (op y.val) m.val)
    (fun a m x => (mul_smul (op x.val) (op a.val) m.val).symm)

private def multiplication (e : Idempotent R)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Tensor (Corner e) (moduleCorner (M := M) e) (rightIdeal e) →ₗ[Rᵐᵒᵖ] M where
  __ := lift (multiplicationPairing e M)
  map_smul' a z := lift_rightScale (multiplicationPairing e M)
    (fun b m x => mul_smul b (op x.val) m.val) a z

@[simp] private theorem multiplication_tmul (e : Idempotent R)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] (m : moduleCorner (M := M) e) (x : rightIdeal e) :
    multiplication e M (tmul (Corner e) m x) = op x.val • m.val := rfl

private def expand (e : Idempotent R) (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {n : ℕ} (r s : Fin n → R) :
    M →+ Tensor (Corner e) (moduleCorner (M := M) e) (rightIdeal e) where
  toFun m := ∑ i, tmul (Corner e) (toModuleCorner e (op (r i) • m))
    (op (s i) • rightGenerator e)
  map_zero' := by simp [zero_tmul]
  map_add' m m' := by simp [smul_add, add_tmul, Finset.sum_add_distrib]

private theorem multiplication_expand (e : Idempotent R)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {n : ℕ} (r s : Fin n → R) (h : (∑ i, r i * e.val * s i) = 1) (m : M) :
    multiplication e M (expand e M r s m) = m := by
  change multiplication e M (∑ i, tmul (Corner e) (toModuleCorner e (op (r i) • m))
    (op (s i) • rightGenerator e)) = m
  rw [map_sum]
  simp only [multiplication_tmul]
  change (∑ i, op (e.val * s i) • (op e.val • (op (r i) • m))) = m
  have combine (i : Fin n) :
      (r i * e.val) * (e.val * s i) = r i * e.val * s i := by
    rw [mul_assoc (r i), ← mul_assoc e.val e.val, e.property.eq, mul_assoc]
  simp only [← mul_smul, ← op_mul, combine]
  rw [← Finset.sum_smul, ← Finset.op_sum, h, op_one, one_smul]

private theorem expand_multiplication (e : Idempotent R)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {n : ℕ} (r s : Fin n → R) (h : (∑ i, r i * e.val * s i) = 1)
    (z : Tensor (Corner e) (moduleCorner (M := M) e) (rightIdeal e)) :
    expand e M r s (multiplication e M z) = z := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ha z z' hz hz' => simp [map_add, hz, hz']
  | ht m x =>
    simp only [multiplication_tmul]
    change (∑ i, tmul (Corner e) (toModuleCorner e (op (r i) • (op x.val • m.val)))
      (op (s i) • rightGenerator e)) = tmul (Corner e) m x
    have hLeft (i : Fin n) :
        toModuleCorner e (op (r i) • (op x.val • m.val)) =
          op (projectToCorner e (op (r i) • x)) • m := by
      apply Subtype.ext
      change op e.val • (op (r i) • (op x.val • m.val)) =
        op (x.val * r i * e.val) • m.val
      simp only [← mul_smul, ← op_mul, mul_assoc]
    have hRight (i : Fin n) :
        projectToCorner e (op (r i) • x) • (op (s i) • rightGenerator e) =
          op (r i * e.val * s i) • x := by
      apply Subtype.ext
      change (x.val * r i * e.val) * (e.val * s i) = x.val * (r i * e.val * s i)
      rw [mul_assoc (x.val * r i), ← mul_assoc e.val e.val, e.property.eq]
      simp only [mul_assoc]
    simp only [hLeft, balance, hRight]
    change (∑ i, pairing.toBiadditive m (op (r i * e.val * s i) • x)) = _
    rw [← map_sum, ← Finset.sum_smul, ← Finset.op_sum, h, op_one, one_smul]
    rfl

private theorem multiplication_bijective (e : Idempotent R) (he : IsFull e)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] : Function.Bijective (multiplication e M) := by
  obtain ⟨n, r, s, h⟩ := (full_iff_sum e).mp he
  exact ⟨Function.LeftInverse.injective (expand_multiplication e M r s h),
    Function.RightInverse.surjective (multiplication_expand e M r s h)⟩

private noncomputable def multiplicationEquiv (e : Idempotent R) (he : IsFull e)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Tensor (Corner e) (moduleCorner (M := M) e) (rightIdeal e) ≃ₗ[Rᵐᵒᵖ] M :=
  LinearEquiv.ofBijective (multiplication e M) (multiplication_bijective e he M)

private theorem multiplicationEquiv_symm_apply (e : Idempotent R) (he : IsFull e)
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] {n : ℕ} (r s : Fin n → R)
    (h : (∑ i, r i * e.val * s i) = 1) (m : M) :
    (multiplicationEquiv e he M).symm m =
      ∑ i, tmul (Corner e) (toModuleCorner e (op (r i) • m)) (op (s i) • rightGenerator e) := by
  change (multiplicationEquiv e he M).symm m = expand e M r s m
  apply (multiplicationEquiv e he M).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (multiplication_expand e M r s h m).symm

theorem full_corner_multiplication : FullEquivalenceSpec.multiplicationEquivType.{u,v} := by
  intro R _ e he M _ _
  refine ⟨multiplicationEquiv e he M, multiplication_tmul e M, ?_⟩
  intro n r s h m
  exact multiplicationEquiv_symm_apply e he M r s h m

/-- The natural multiplication isomorphism from (Me) ⊗[eRe] eR to M. -/
noncomputable def fullCornerMultiplicationIso (e : Idempotent R) (he : IsFull e) :
    cornerFunctor.{u,max u v} e ⋙ fromCornerFunctor e ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => (multiplicationEquiv e he M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro m x
    change multiplication e N (tmul (Corner e) (restrictToCorner e f.hom m) x) =
      f (multiplication e M (tmul (Corner e) m x))
    exact (f.hom.map_smul (op x.val) m.val).symm)

@[simp] theorem fullCornerMultiplicationIso_hom_tmul (e : Idempotent R) (he : IsFull e)
    (M : ModuleCat.{max u v} Rᵐᵒᵖ) (m : moduleCorner (M := M) e) (x : rightIdeal e) :
    (fullCornerMultiplicationIso e he).hom.app M (tmul (Corner e) m x) =
      op x.val • m.val := rfl

theorem fullCornerMultiplicationIso_inv_apply (e : Idempotent R) (he : IsFull e)
    (M : ModuleCat.{max u v} Rᵐᵒᵖ) {n : ℕ} (r s : Fin n → R)
    (h : (∑ i, r i * e.val * s i) = 1) (m : M) :
    (fullCornerMultiplicationIso e he).inv.app M m =
      ∑ i, tmul (Corner e) (toModuleCorner e (op (r i) • m)) (op (s i) • rightGenerator e) :=
  multiplicationEquiv_symm_apply e he M r s h m

private def contractionPairing (e : Idempotent R)
    (N : Type v) [AddCommGroup N] [Module (Corner e)ᵐᵒᵖ N] :
    Pairing (Corner e) (A := N) (B := rightIdeal e) N :=
  Pairing.ofFun (fun n x => op (projectToCorner e x) • n)
    (fun n n' x => smul_add (op (projectToCorner e x)) n n')
    (fun n x y => by
      have h : projectToCorner e (x + y) = projectToCorner e x + projectToCorner e y :=
        Subtype.ext (add_mul x.val y.val e.val)
      rw [h]
      exact add_smul (op (projectToCorner e x)) (op (projectToCorner e y)) n)
    (fun a n x => by
      have h : projectToCorner e (a • x) = a * projectToCorner e x :=
        Subtype.ext (mul_assoc a.val x.val e.val)
      rw [h, op_mul, mul_smul])

private def contraction (e : Idempotent R)
    (N : Type v) [AddCommGroup N] [Module (Corner e)ᵐᵒᵖ N] :
    Tensor (Corner e) N (rightIdeal e) →+ N :=
  lift (contractionPairing e N)

@[simp] private theorem contraction_tmul (e : Idempotent R)
    (N : Type v) [AddCommGroup N] [Module (Corner e)ᵐᵒᵖ N] (n : N) (x : rightIdeal e) :
    contraction e N (tmul (Corner e) n x) = op (projectToCorner e x) • n := rfl

private theorem contraction_smul (e : Idempotent R)
    (N : Type v) [AddCommGroup N] [Module (Corner e)ᵐᵒᵖ N]
    (a : (Corner e)ᵐᵒᵖ) (z : Tensor (Corner e) N (rightIdeal e)) :
    contraction e N (op a.unop.val • z) = a • contraction e N z := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ha z z' hz hz' => simp [smul_add, hz, hz']
  | ht n x =>
    change contraction e N (tmul (Corner e) n (op a.unop.val • x)) = _
    have h : projectToCorner e (op a.unop.val • x) = projectToCorner e x * a.unop := by
      apply Subtype.ext
      change (x.val * a.unop.val) * e.val = (x.val * e.val) * a.unop.val
      rw [mul_assoc, a.unop.property.2, mul_assoc, a.unop.property.1]
    simp only [contraction_tmul, h, op_mul, op_unop, mul_smul]

private theorem tensor_contraction (e : Idempotent R)
    (N : Type v) [AddCommGroup N] [Module (Corner e)ᵐᵒᵖ N]
    (z : Tensor (Corner e) N (rightIdeal e)) :
    tmul (Corner e) (contraction e N z) (rightGenerator e) = op e.val • z := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp [zero_tmul]
  | ha z z' hz hz' => simp [add_tmul, smul_add, hz, hz']
  | ht n x =>
    simp only [contraction_tmul, balance]
    change tmul (Corner e) n (projectToCorner e x • rightGenerator e) =
      tmul (Corner e) n (op e.val • x)
    have h : projectToCorner e x • rightGenerator e = op e.val • x :=
      Subtype.ext (projectToCorner e x).property.2
    rw [h]

private def extensionCornerEquiv (e : Idempotent R)
    (N : Type v) [AddCommGroup N] [Module (Corner e)ᵐᵒᵖ N] :
    moduleCorner (M := Tensor (Corner e) N (rightIdeal e)) e ≃ₗ[(Corner e)ᵐᵒᵖ] N where
  toFun z := contraction e N z.val
  map_add' z z' := (contraction e N).map_add z.val z'.val
  map_smul' a z := contraction_smul e N a z.val
  invFun n := ⟨tmul (Corner e) n (rightGenerator e), by
    change tmul (Corner e) n (op e.val • rightGenerator e) = _
    exact congrArg (tmul (Corner e) n) (Subtype.ext e.property)⟩
  left_inv z := Subtype.ext ((tensor_contraction e N z.val).trans z.property)
  right_inv n := by
    change op (projectToCorner e (rightGenerator e)) • n = n
    rw [show projectToCorner e (rightGenerator e) = 1 from Subtype.ext e.property]
    simp

/-- Restricting the extended module to the corner recovers the original module. -/
def cornerExtensionIso (e : Idempotent R) :
    fromCornerFunctor.{u,v} e ⋙ cornerFunctor e ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N => (extensionCornerEquiv e N).toModuleIso) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change contraction e N' (map f.hom LinearMap.id z.val) = f.hom (contraction e N z.val)
    generalize z.val = t
    induction t using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ha t t' ht ht' => simp [ht, ht']
    | ht n x => simp [map_smul])

private theorem contraction_multiplication (e : Idempotent R) (M : ModuleCat.{max u v} Rᵐᵒᵖ)
    (z : Tensor (Corner e) (moduleCorner (M := M) e) (rightIdeal e)) :
    (contraction e (moduleCorner (M := M) e) z).val = op e.val • multiplication e M z := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ha z z' hz hz' =>
    rw [map_add, map_add, smul_add]
    exact congrArg₂ (· + ·) hz hz'
  | ht m x =>
    change op (x.val * e.val) • m.val = op e.val • (op x.val • m.val)
    exact mul_smul (op e.val) (op x.val) m.val

private theorem multiplication_triangle (e : Idempotent R) (he : IsFull e)
    (M : ModuleCat.{max u v} Rᵐᵒᵖ) :
    (cornerFunctor e).map ((fullCornerMultiplicationIso e he).hom.app M) =
      (cornerExtensionIso e).hom.app ((cornerFunctor e).obj M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change multiplication e M z.val = (contraction e (moduleCorner (M := M) e) z.val).val
  exact (congrArg (multiplication e M) z.property.symm).trans
    (((multiplication e M).map_smul (op e.val) z.val).trans
      (contraction_multiplication e M z.val).symm)

/-- Taking the corner and extending by eR are inverse equivalences for full e. -/
noncomputable def fullCornerEquivalence (e : Idempotent R) (he : IsFull e) :
    ModuleCat.{max u v} Rᵐᵒᵖ ≌ ModuleCat.{max u v} (Corner e)ᵐᵒᵖ where
  functor := cornerFunctor e
  inverse := fromCornerFunctor e
  unitIso := (fullCornerMultiplicationIso e he).symm
  counitIso := cornerExtensionIso e
  functor_unitIso_comp M := by
    change (cornerFunctor e).map ((fullCornerMultiplicationIso e he).inv.app M) ≫
      (cornerExtensionIso e).hom.app ((cornerFunctor e).obj M) = 𝟙 _
    rw [← multiplication_triangle e he M, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact (cornerFunctor e).map_id M

theorem full_corner_equivalence : FullEquivalenceSpec.fullEquivalenceType.{u,v} := by
  intro R _ e he
  refine ⟨fullCornerEquivalence e he, rfl, rfl, ?_, ?_⟩
  · exact fullCornerMultiplicationIso_hom_tmul e he
  · intro M n r s h m
    exact fullCornerMultiplicationIso_inv_apply e he M r s h m

end RM03.Morita
