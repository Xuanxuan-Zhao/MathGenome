import MathGenome.Internal.Specs.D07.Ch22.TensorConstruction
import Mathlib.Algebra.Module.TransferInstance

/-!
# The balanced tensor quotient

K07.22.tensor_construction. The source's free abelian quotient is proved
isomorphic to the canonical tensor product, with specified elementary tensors.
The two universal properties retain their different target hypotheses.
-/

noncomputable section
universe u v w t
namespace D07.Ch22.TensorConstruction
open Specs.D07.Ch22.TensorConstruction
open scoped TensorProduct

section Helpers
variable {M : Type v} {N : Type w} {A : Type t} [AddCommGroup A]

@[simp] theorem freeExtension_symbol (b : M → N → A) (m : M) (n : N) :
    freeExtension b (symbol m n) = b m n := by
  simp [freeExtension, symbol]

/-- Additive maps from the free abelian group are determined by its symbols. -/
theorem freeHom_ext {F G : FreeAbelian M N →+ A}
    (h : ∀ m n, F (symbol m n) = G (symbol m n)) : F = G := by
  apply Finsupp.addHom_ext
  intro p z
  rw [← Finsupp.smul_single_one p z, map_zsmul, map_zsmul]
  exact congrArg (fun a => z • a) (h p.1 p.2)

variable {R : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Killing the generators is equivalent to killing their generated subgroup. -/
theorem relations_le_ker (F : FreeAbelian M N →+ A)
    (h : ∀ x, DefiningRelation R M N x → F x = 0) :
    relationSubgroup R M N ≤ F.ker :=
  (AddSubgroup.closure_le F.ker).mpr h

/-- Equality modulo the displayed relations makes each defining difference zero. -/
theorem projection_relation {x : FreeAbelian M N} (h : DefiningRelation R M N x) :
    projection R M N x = 0 :=
  (QuotientAddGroup.eq_zero_iff x).mpr (AddSubgroup.subset_closure h)

/-- Package a balanced function as a homomorphism in each argument. -/
def balancedHom (b : M → N → A) (h : IsBalanced R M N b) : M →+ N →+ A :=
  AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (b m) (h.add_right m))
    (fun m m' => AddMonoidHom.ext (fun n => h.add_left m m' n))

/-- The free extension of a balanced function kills all three families. -/
theorem balanced_kills (b : M → N → A) (h : IsBalanced R M N b)
    (x : FreeAbelian M N) (hx : DefiningRelation R M N x) : freeExtension b x = 0 := by
  cases hx with
  | addLeft m m' n => simp [h.add_left, sub_sub]
  | addRight m n n' => simp [h.add_right, sub_sub]
  | balance r m n => simp [h.balance]

/-- Elementary tensors satisfy the balanced identities, before any target lift. -/
theorem canonicalBalanced : IsBalanced R M N (fun m n => m ⊗ₜ[R] n) :=
  ⟨TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul⟩
end Helpers

theorem quotientBalanced : QuotientBalanced.{u, v, w} := by
  intro R _ M N _ _ _ _
  constructor
  · intro m m' n
    have h := projection_relation (DefiningRelation.addLeft (R := R) m m' n)
    simp only [map_sub] at h
    change tensorClass R M N (m + m') n - tensorClass R M N m n -
      tensorClass R M N m' n = 0 at h
    simpa only [sub_sub, sub_eq_zero] using h
  · intro m n n'
    have h := projection_relation (DefiningRelation.addRight (R := R) m n n')
    simp only [map_sub] at h
    change tensorClass R M N m (n + n') - tensorClass R M N m n -
      tensorClass R M N m n' = 0 at h
    simpa only [sub_sub, sub_eq_zero] using h
  · intro r m n
    have h := projection_relation (DefiningRelation.balance r m n)
    simpa only [map_sub, sub_eq_zero, tensorClass] using h

theorem factorCriterion : FactorCriterion.{u, v, w, t} := by
  intro R _ M N _ _ _ _ A _ F
  constructor
  · intro h
    refine ⟨QuotientAddGroup.lift _ F (relations_le_ker F h), fun _ => rfl, ?_⟩
    intro g hg
    apply QuotientAddGroup.addMonoidHom_ext
    exact AddMonoidHom.ext hg
  · rintro ⟨f, hf, _⟩ x hx
    rw [← hf, projection_relation hx, map_zero]

theorem quotientUniversalProperty : QuotientUniversalProperty.{u, v, w, t} := by
  intro R _ M N _ _ _ _ A _ b hb
  obtain ⟨F, hF, _⟩ := (factorCriterion R M N A (freeExtension b)).mp (balanced_kills b hb)
  refine ⟨F, ?_, ?_⟩
  · intro m n
    exact (hF (symbol m n)).trans (freeExtension_symbol b m n)
  · intro G hG
    apply QuotientAddGroup.addMonoidHom_ext
    apply freeHom_ext
    intro m n
    exact (hG m n).trans ((hF (symbol m n)).trans (freeExtension_symbol b m n)).symm

theorem balancedUniversalProperty : BalancedUniversalProperty.{u, v, w, t} := by
  intro R _ M N _ _ _ _ A _ b hb
  let F := TensorProduct.liftAddHom (balancedHom b hb) hb.balance
  refine ⟨F, fun _ _ => rfl, ?_⟩
  intro G hG
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact hG m n
  | add x y hx hy => simp only [map_add, hx, hy]

theorem quotientPresentation : QuotientPresentation.{u, v, w} := by
  intro R _ M N _ _ _ _
  obtain ⟨F, hF, uniqF⟩ := quotientUniversalProperty R M N (M ⊗[R] N)
    (fun m n => m ⊗ₜ[R] n) canonicalBalanced
  obtain ⟨G, hG, uniqG⟩ := balancedUniversalProperty R M N (PresentedTensor R M N)
    (tensorClass R M N) (quotientBalanced R M N)
  have hGF : G.comp F = AddMonoidHom.id _ := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply freeHom_ext
    intro m n
    change G (F (tensorClass R M N m n)) = tensorClass R M N m n
    rw [hF, hG]
  have hFG : F.comp G = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp only [AddMonoidHom.comp_apply, hG, hF, AddMonoidHom.id_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨{ F with invFun := G, left_inv := ?_, right_inv := ?_ }, hF⟩
  · exact DFunLike.congr_fun hGF
  · exact DFunLike.congr_fun hFG

theorem tensorGenerators : TensorGenerators.{u, v, w} := by
  intro R _ M N _ _ _ _
  refine top_unique fun x _ => ?_
  exact TensorProduct.inductionOn x
    (fun m n => AddSubgroup.subset_closure ⟨m, n, rfl⟩)
    (fun _ _ hx hy => AddSubgroup.add_mem _ hx hy)

theorem quotientGenerators : QuotientGenerators.{u, v, w} := by
  intro R _ M N _ _ _ _
  obtain ⟨e, he⟩ := quotientPresentation R M N
  apply top_unique
  intro x _
  have h (y : M ⊗[R] N) : e.symm y ∈
      AddSubgroup.closure {x | ∃ m n, tensorClass R M N m n = x} := by
    induction y using TensorProduct.inductionOn with
    | tmul m n =>
      apply AddSubgroup.subset_closure
      exact ⟨m, n, e.eq_symm_apply.mpr (he m n)⟩
    | add x y hx hy => simpa only [map_add] using AddSubgroup.add_mem _ hx hy
  simpa only [e.symm_apply_apply] using h (e x)

/-- Commutativity is used in the balancing-generator case: r(s m) = s(r m). -/
theorem scalarRelationInvariant : ScalarRelationInvariant.{u, v, w} := by
  intro R _ M N _ _ _ _ r x hx
  have hmap : relationSubgroup R M N ≤
      (relationSubgroup R M N).comap (freeScalar R M N r) := by
    apply (AddSubgroup.closure_le _).mpr
    intro y hy
    change freeScalar R M N r y ∈ relationSubgroup R M N
    cases hy with
    | addLeft m m' n =>
      simp only [map_sub, freeScalar, freeExtension_symbol, smul_add]
      exact AddSubgroup.subset_closure (DefiningRelation.addLeft (R := R) (r • m) (r • m') n)
    | addRight m n n' =>
      simp only [map_sub, freeScalar, freeExtension_symbol]
      exact AddSubgroup.subset_closure (DefiningRelation.addRight (R := R) (r • m) n n')
    | balance s m n =>
      simp only [map_sub, freeScalar, freeExtension_symbol]
      rw [smul_comm r s m]
      exact AddSubgroup.subset_closure (DefiningRelation.balance s (r • m) n)
  exact hmap hx

/-- Transport along the proved presentation equivalence retains the quotient's
original addition, and its action is the actual descent on free representatives. -/
theorem quotientModuleConstruction : QuotientModuleConstruction.{u, v, w} := by
  intro R _ M N _ _ _ _
  obtain ⟨e, he⟩ := quotientPresentation R M N
  let : Module R (PresentedTensor R M N) := e.module R
  let el : PresentedTensor R M N ≃ₗ[R] (M ⊗[R] N) := e.linearEquiv R
  have ht (r : R) (m : M) (n : N) :
      r • tensorClass R M N m n = tensorClass R M N (r • m) n := by
    apply el.injective
    rw [el.map_smul]
    change r • e (tensorClass R M N m n) = e (tensorClass R M N (r • m) n)
    rw [he, he]
    rfl
  refine ⟨inferInstance, ?_, ht, ?_, el, he⟩
  · intro r x
    have hmap : (DistribSMul.toAddMonoidHom (PresentedTensor R M N) r).comp
        (projection R M N) = (projection R M N).comp (freeScalar R M N r) := by
      apply freeHom_ext
      intro m n
      change r • tensorClass R M N m n =
        projection R M N (freeScalar R M N r (symbol m n))
      simpa only [freeScalar, freeExtension_symbol, tensorClass] using ht r m n
    exact DFunLike.congr_fun hmap x
  · exact ⟨one_smul R, mul_smul, add_smul, smul_add⟩

theorem tensorModuleLaws : TensorModuleLaws.{u, v, w} := by
  intro R _ M N _ _ _ _
  exact ⟨⟨one_smul R, mul_smul, add_smul, smul_add⟩, fun _ _ _ => rfl⟩

theorem bilinearBalanced : BilinearBalanced.{u, v, w, t} := by
  intro R _ M N _ _ _ _ P _ _ b
  refine ⟨?_, ?_, ?_⟩
  · intro m m' n
    exact congrArg (fun f : N →ₗ[R] P => f n) (b.map_add m m')
  · intro m n n'
    exact (b m).map_add n n'
  · intro r m n
    calc
      b (r • m) n = (r • b m) n := congrArg (fun f : N →ₗ[R] P => f n) (b.map_smul r m)
      _ = r • b m n := rfl
      _ = b m (r • n) := ((b m).map_smul r n).symm

theorem additiveLiftLinear : AdditiveLiftLinear.{u, v, w, t} := by
  intro R _ M N _ _ _ _ P _ _ b F hF r x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
    rw [TensorProduct.smul_tmul', hF, hF]
    exact congrArg (fun f : N →ₗ[R] P => f n) (b.map_smul r m)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem linearUniversalProperty : LinearUniversalProperty.{u, v, w, t} := by
  intro R _ M N _ _ _ _ P _ _ b
  exact ⟨TensorProduct.lift b, fun _ _ => rfl, fun _ h => TensorProduct.lift.unique h⟩

theorem homBilinearEquivalence : HomBilinearEquivalence.{u, v, w, t} := by
  intro R _ M N _ _ _ _ P _ _
  exact ⟨(TensorProduct.lift.equiv (RingHom.id R) M N P).symm, fun _ _ _ => rfl⟩

end D07.Ch22.TensorConstruction
