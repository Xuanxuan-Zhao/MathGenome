import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectHomBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.Data.Int.Interval

open CategoryTheory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct

universe u v w
namespace DerivedFormalization.Descent

open Specs.DerivedFormalization.Descent.PerfectHomBaseChange

variable {A : Type u} (S : Type v) [CommRing A] [CommRing S] [Algebra A S]

/-- The strict comparison for ordinary signed cochain Hom. -/
abbrev homBaseChange (A : Type u) (S : Type v) [CommRing A] [CommRing S] [Algebra A S]
    (P X : Comp.{w} A) :=
  comparison S P X

theorem homBaseChange_apply : comparison_applyType.{u,v,w} := by
  intro A S _ _ _ P X n i j hij s t f p
  let : Module A (Cochain ((extend A S).obj P) ((extend A S).obj X) n) :=
    Module.restrictScalars A S _
  let : IsScalarTower A S (Cochain ((extend A S).obj P) ((extend A S).obj X) n) :=
    IsScalarTower.restrictScalars A S _
  change (((extendCochain S n).liftBaseChange S (s ⊗ₜ[A] f)).v i j hij) (t ⊗ₜ[A] p) = _
  rw [LinearMap.liftBaseChange_tmul, Cochain.smul_v]
  change s • (f.v i j hij).hom.baseChange S (t ⊗ₜ[A] p) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  rfl

private theorem tensor_maps_ext {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module S N] {g h : S ⊗[A] M →ₗ[S] N}
    (e : ∀ s m, g (s ⊗ₜ[A] m) = h (s ⊗ₜ[A] m)) : g = h := by
  let : Module A N := Module.restrictScalars A S N
  let : IsScalarTower A S N := IsScalarTower.restrictScalars A S N
  exact TensorProduct.AlgebraTensorModule.ext e

section Modules

variable {M N F : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup F]
  [Module A M] [Module A N] [Module A F]

private def moduleComparison :
    S ⊗[A] (M →ₗ[A] N) →ₗ[S] (S ⊗[A] M →ₗ[S] S ⊗[A] N) :=
  (LinearMap.baseChangeHom A S M N).liftBaseChange S

@[simp] private theorem moduleComparison_tmul (s t : S) (f : M →ₗ[A] N) (x : M) :
    moduleComparison S (s ⊗ₜ[A] f) (t ⊗ₜ[A] x) = (s * t) ⊗ₜ[A] f x := by
  simp [moduleComparison, TensorProduct.smul_tmul']

private theorem moduleComparison_free [Module.Free A M] [Module.Finite A M] :
    Function.Bijective (moduleComparison (A := A) S (M := M) (N := N)) := by
  let α := TensorProduct.mk A S M 1
  let β := TensorProduct.mk A S N 1
  have hα : IsBaseChange S α := TensorProduct.isBaseChange A M S
  have hβ : IsBaseChange S β := TensorProduct.isBaseChange A N S
  let e := (IsBaseChange.linearMapLeftRight hα hβ).equiv
  suffices h : moduleComparison S = e.toLinearMap by
    rw [h]
    exact e.bijective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s f
  apply hα.algHom_ext
  intro x
  change moduleComparison S (s ⊗ₜ[A] f) (1 ⊗ₜ[A] x) = e (s ⊗ₜ[A] f) (α x)
  simp [e, IsBaseChange.equiv_tmul, IsBaseChange.linearMapLeftRightHom_comp_apply,
    β, TensorProduct.smul_tmul']

private def precompose (g : F →ₗ[A] M) : (M →ₗ[A] N) →ₗ[A] (F →ₗ[A] N) :=
  (LinearMap.llcomp A F M N).flip g

private theorem moduleComparison_precompose (g : F →ₗ[A] M)
    (z : S ⊗[A] (M →ₗ[A] N)) :
    moduleComparison S ((precompose g).baseChange S z) =
      (moduleComparison S z).comp (g.baseChange S) := by
  have hh : moduleComparison S ∘ₗ (precompose g (N := N)).baseChange S =
      (precompose (A := S) (g.baseChange S)) ∘ₗ moduleComparison S := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s f
    apply TensorProduct.AlgebraTensorModule.ext
    intro t x
    simp [precompose]
  exact LinearMap.congr_fun hh z

private theorem precompose_retract (p : F →ₗ[A] M) (i : M →ₗ[A] F)
    (hp : p.comp i = LinearMap.id) :
    (precompose i (N := N)).comp (precompose p) = LinearMap.id := by
  ext f x
  have hx := LinearMap.congr_fun hp x
  change p (i x) = x at hx
  change f (p (i x)) = f x
  rw [hx]

private theorem moduleComparison_projective [Module.Finite A M] [Module.Projective A M] :
    Function.Bijective (moduleComparison (A := A) S (M := M) (N := N)) := by
  obtain ⟨n, p, i, _, _, hp⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  have hfree := moduleComparison_free (A := A) S (M := Fin n → A) (N := N)
  have hps : (p.baseChange S).comp (i.baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hp, LinearMap.baseChange_id]
  have hretract (z : S ⊗[A] (M →ₗ[A] N)) :
      (precompose i).baseChange S ((precompose p).baseChange S z) = z := by
    change (((precompose i).baseChange S).comp ((precompose p).baseChange S)) z = z
    rw [← LinearMap.baseChange_comp, precompose_retract p i hp, LinearMap.baseChange_id]
    rfl
  constructor
  · intro x y h
    have hxy : (precompose p).baseChange S x = (precompose p).baseChange S y := by
      apply hfree.1
      rw [moduleComparison_precompose, moduleComparison_precompose, h]
    simpa only [hretract] using congrArg ((precompose i (N := N)).baseChange S) hxy
  · intro f
    obtain ⟨z, hz⟩ := hfree.2 (f.comp (p.baseChange S))
    refine ⟨(precompose i).baseChange S z, ?_⟩
    rw [moduleComparison_precompose, hz, LinearMap.comp_assoc, hps, LinearMap.comp_id]

end Modules

private def restrictProduct {R : Type*} [CommRing R] (I : Finset ℤ)
    (M : ℤ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (h : ∀ i ∉ I, Subsingleton (M i)) :
    (∀ i, M i) ≃ₗ[R] (∀ i : I, M i) where
  toFun f i := f i
  invFun f i := if hi : i ∈ I then f ⟨i, hi⟩ else 0
  left_inv f := by
    funext i
    by_cases hi : i ∈ I
    · simp [hi]
    · have := h i hi
      exact Subsingleton.elim _ _
  right_inv f := by
    funext i
    exact dite_eq_left i.property
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem subsingleton_tensor {M : Type*} [AddCommGroup M] [Module A M]
    [Subsingleton M] : Subsingleton (S ⊗[A] M) := by
  apply subsingleton_of_forall_eq (0 : S ⊗[A] M)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s x => simp [Subsingleton.elim x 0]
  | add x y hx hy => simp [hx, hy]

private theorem subsingleton_linearMaps {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Subsingleton M] [AddCommGroup N] [Module R N] :
    Subsingleton (M →ₗ[R] N) := by
  apply subsingleton_of_forall_eq (0 : M →ₗ[R] N)
  intro f
  ext x
  rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem homBaseChange_isIso : comparison_isIsoType.{u,v,w} := by
  intro A S _ _ _ P X ⟨L, U, hbounds⟩ hfinite hprojective
  let I := Finset.Icc L U
  have hz (i : ℤ) (hi : i ∉ I) : Subsingleton (P.X i) := by
    apply hbounds
    simpa only [I, Finset.mem_Icc, not_and_or, not_le] using hi
  refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ (comparison S P X) ?_
  intro n
  classical
  let M (i : ℤ) := P.X i →ₗ[A] X.X (i + n)
  let N (i : ℤ) := (S ⊗[A] P.X i) →ₗ[S] (S ⊗[A] X.X (i + n))
  let e₁ : Cochain P X n ≃ₗ[A] (∀ i : I, M i) :=
    (DerivedFormalization.internalHomProduct P X n).trans
      (restrictProduct I M fun i hi => by
        have := hz i hi
        exact subsingleton_linearMaps)
  let e₂ : Cochain ((extend A S).obj P) ((extend A S).obj X) n ≃ₗ[S]
      (∀ i : I, N i) :=
    (DerivedFormalization.internalHomProduct ((extend A S).obj P) ((extend A S).obj X) n).trans
      (restrictProduct I N fun i hi => by
        have := hz i hi
        have := subsingleton_tensor (A := A) S (M := P.X i)
        exact subsingleton_linearMaps)
  let eᵢ (i : I) : S ⊗[A] M i ≃ₗ[S] N i := by
    have := hfinite i
    have := hprojective i
    exact LinearEquiv.ofBijective _ (moduleComparison_projective (A := A) S)
  let e : S ⊗[A] Cochain P X n ≃ₗ[S]
      Cochain ((extend A S).obj P) ((extend A S).obj X) n :=
    (e₁.baseChange A S _ _).trans <|
      (TensorProduct.piRight A S S (fun i : I => M i)).trans <|
        (LinearEquiv.piCongrRight eᵢ).trans e₂.symm
  have he : ((comparison S P X).f n).hom = e.toLinearMap := by
    apply tensor_maps_ext (A := A) S
    intro s f
    apply e₂.injective
    funext i
    apply tensor_maps_ext (A := A) S
    intro t p
    change ((comparison S P X).f n (s ⊗ₜ[A] f)).v i (i.val + n) rfl (t ⊗ₜ[A] p) =
      (e₂ (e (s ⊗ₜ[A] f)) i) (t ⊗ₜ[A] p)
    rw [homBaseChange_apply A S]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply,
      LinearEquiv.apply_symm_apply, eᵢ, LinearEquiv.ofBijective_apply]
    rfl
  have he' : (comparison S P X).f n = e.toModuleIso.hom :=
    ModuleCat.hom_ext he
  rw [he']
  exact e.toModuleIso.isIso_hom

set_option backward.isDefEq.respectTransparency false in
theorem homBaseChange_natural : comparison_naturalType.{u,v,w} := by
  intro A S _ _ _ P P' X X' g h
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply tensor_maps_ext (A := A) S
  intro s f
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply tensor_maps_ext (A := A) S
  intro t p
  change ((comparison S P' X').f n
      (s ⊗ₜ[A] (DerivedFormalization.internalHomMap g h).f n f)).v i j hij (t ⊗ₜ[A] p) =
    ((DerivedFormalization.internalHomMap ((extend A S).map g) ((extend A S).map h)).f n
      ((comparison S P X).f n (s ⊗ₜ[A] f))).v i j hij (t ⊗ₜ[A] p)
  simp only [homBaseChange_apply A S, DerivedFormalization.internalHomMap_apply,
    extend_map_tmul]

theorem homBaseChange_unit : comparison_unitType.{u,w} := by
  intro A _ P X
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply tensor_maps_ext (A := A) A
  intro a f
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  change ((DerivedFormalization.internalHomMap (extendId A P).inv (extendId A X).hom).f n
      ((comparison A P X).f n (a ⊗ₜ[A] f))).v i j hij p =
    ((extendId A (internalHom P X)).hom.f n (a ⊗ₜ[A] f)).v i j hij p
  simp only [DerivedFormalization.internalHomMap_apply, extendId_inv_apply,
    homBaseChange_apply A A, mul_one, extendId_hom_tmul]
  rfl

private theorem iterated_tensor_maps_ext {A S T M N : Type*}
    [CommRing A] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    [Algebra S T] [IsScalarTower A S T] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module T N] {g h : T ⊗[S] (S ⊗[A] M) →ₗ[T] N}
    (H : ∀ t m, g (t ⊗ₜ[S] (1 ⊗ₜ[A] m)) = h (t ⊗ₜ[S] (1 ⊗ₜ[A] m))) : g = h := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M
  have he : g.comp e.symm.toLinearMap = h.comp e.symm.toLinearMap := by
    apply tensor_maps_ext (A := A) T
    intro t m
    exact H t m
  ext z
  obtain ⟨y, rfl⟩ := e.symm.surjective z
  exact LinearMap.congr_fun he y

set_option backward.isDefEq.respectTransparency false in
theorem homBaseChange_tower : comparison_towerType.{u,v,w} := by
  intro A S T _ _ _ _ _ _ _ P X
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply iterated_tensor_maps_ext (A := A) (S := S) (T := T)
  intro t f
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply tensor_maps_ext (A := A) T
  intro r p
  change ((DerivedFormalization.internalHomMap (extendComp A S T P).inv
      (extendComp A S T X).hom).f n
      ((comparison T ((extend A S).obj P) ((extend A S).obj X)).f n
        (((extend S T).map (comparison S P X)).f n (t ⊗ₜ[S] (1 ⊗ₜ[A] f))))).v
          i j hij (r ⊗ₜ[A] p) =
    ((comparison T P X).f n
      ((extendComp A S T (internalHom P X)).hom.f n (t ⊗ₜ[S] (1 ⊗ₜ[A] f)))).v
        i j hij (r ⊗ₜ[A] p)
  simp only [DerivedFormalization.internalHomMap_apply, extendComp_inv_tmul, extend_map_tmul,
    homBaseChange_apply S T, homBaseChange_apply A S, homBaseChange_apply A T,
    extendComp_hom_tmul, one_mul, one_smul]

private theorem extensionUnit_natural
    (A : Type u) (S T : Type v) [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    {Y Z : Comp.{max v w} S} (g : Y ⟶ Z) :
    (restrict A S).map g ≫ extensionUnit A S T Z =
      extensionUnit A S T Y ≫ (restrict A T).map ((extend S T).map g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rfl

theorem changeCoefficients_apply : changeCoefficients_applyType.{u,v,w} := by
  intro A S T _ _ _ _ _ φ X i s x
  let : Algebra S T := φ.toRingHom.toAlgebra
  change ((s • (1 : T)) ⊗ₜ[A] x : T ⊗[A] X.X i) = φ s ⊗ₜ[A] x
  change (φ s * 1) ⊗ₜ[A] x = φ s ⊗ₜ[A] x
  rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
theorem changeHomCoefficients_apply : changeHomCoefficients_applyType.{u,v,w} := by
  intro A S T _ _ _ _ _ φ P X n i j hij f z
  let : Algebra S T := φ.toRingHom.toAlgebra
  let : IsScalarTower A S T := IsScalarTower.of_algHom φ
  change ((internalHomMap (extendComp A S T P).inv (extendComp A S T X).hom).f n
      ((comparison T ((extend A S).obj P) ((extend A S).obj X)).f n
        ((1 : T) ⊗ₜ[S] f))).v i j hij
      ((extendComp A S T P).hom.f i ((1 : T) ⊗ₜ[S] z)) =
    (extendComp A S T X).hom.f j ((1 : T) ⊗ₜ[S] f.v i j hij z)
  have hinv : (extendComp A S T P).inv.f i
      ((extendComp A S T P).hom.f i ((1 : T) ⊗ₜ[S] z)) =
      (1 : T) ⊗ₜ[S] z := by
    have h := HomologicalComplex.congr_hom (extendComp A S T P).hom_inv_id i
    exact ConcreteCategory.congr_hom h ((1 : T) ⊗ₜ[S] z)
  simp only [internalHomMap_apply, hinv, homBaseChange_apply S T, one_mul]

theorem homBaseChange_changeCoefficients : comparison_changeCoefficientsType.{u,v,w} := by
  intro A S T _ _ _ _ _ φ P X
  let : Algebra S T := φ.toRingHom.toAlgebra
  let : IsScalarTower A S T := IsScalarTower.of_algHom φ
  have h := congrArg ((restrict A T).map) (homBaseChange_tower A S T P X)
  simp only [Functor.map_comp] at h
  simp only [changeCoefficients, changeHomCoefficients, Category.assoc]
  rw [← h]
  simp only [← Category.assoc]
  rw [← extensionUnit_natural A S T (comparison S P X)]
  simp only [Functor.map_comp, Category.assoc]

end DerivedFormalization.Descent
