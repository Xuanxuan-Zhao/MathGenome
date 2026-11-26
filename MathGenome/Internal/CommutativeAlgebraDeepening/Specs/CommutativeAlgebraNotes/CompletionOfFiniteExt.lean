import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CommutativeAlgebraNotes.CompletionOfFiniteExt

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The extension-of-scalars functor with the algebra tensor product as its carrier. -/
abbrev extend (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} A where
  obj X := ModuleCat.of A (A ⊗[R] X)
  map f := ModuleCat.ofHom (f.hom.baseChange A)
  map_id _ := ModuleCat.hom_ext (LinearMap.baseChange_id)
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp f.hom g.hom)

abbrev restrict (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} R :=
  ModuleCat.restrictScalars (algebraMap R A)

@[simp]
lemma extend_map_tmul {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (a : A) (x : X) :
    (extend R A).map f (a ⊗ₜ[R] x) = a ⊗ₜ[R] f x := rfl

instance extend_additive : (extend R A).Additive where
  map_add := ModuleCat.hom_ext (LinearMap.baseChange_add _ _)

/-- Tensor–Hom adjunction on module morphisms. -/
def tensorHomEquiv (X : ModuleCat.{u} R) (Y : ModuleCat.{u} A) :
    ((extend R A).obj X ⟶ Y) ≃ (X ⟶ (restrict R A).obj Y) := by
  letI : Module A ((restrict R A).obj Y) := Y.isModule
  letI : IsScalarTower R A ((restrict R A).obj Y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (ModuleCat.homEquiv (M := (extend R A).obj X) (N := Y)).trans
    ((LinearMap.liftBaseChangeEquiv (R := R) (M := X)
      (N := (restrict R A).obj Y) A).symm.toEquiv.trans
      (ModuleCat.homEquiv (M := X) (N := (restrict R A).obj Y)).symm)

@[simp]
lemma tensorHomEquiv_apply {X : ModuleCat.{u} R} {Y : ModuleCat.{u} A}
    (f : (extend R A).obj X ⟶ Y) (x : X) :
    tensorHomEquiv X Y f x = f ((1 : A) ⊗ₜ[R] x) := rfl

/-- Extension and restriction of scalars are adjoint. -/
def adjunction (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    extend R A ⊣ restrict R A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply (tensorHomEquiv X' Y).injective
        rw [Equiv.apply_symm_apply]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change g (f x) =
          tensorHomEquiv X' Y ((extend R A).map f ≫ (tensorHomEquiv X Y).symm g) x
        rw [tensorHomEquiv_apply, ModuleCat.comp_apply, extend_map_tmul,
          ← tensorHomEquiv_apply, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        ext x
        rfl }

instance extend_preservesFiniteColimits : PreservesFiniteColimits (extend R A) := by
  let := (adjunction R A).isLeftAdjoint
  infer_instance

instance extend_preservesFiniteLimits [Module.Flat R A] :
    PreservesFiniteLimits (extend R A) := by
  have h (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) :
      (S.map (extend R A)).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.lTensor_exact A (f := S.f.hom) (g := S.g.hom) hS
  have h' := ((Functor.exact_tfae (extend R A)).out 2 4).mp h
  exact h'.1

private lemma extend_map_smul_id (Y : ModuleCat.{u} R) (r : R) :
    (extend R A).map (r • 𝟙 Y) = (algebraMap R A r) • 𝟙 ((extend R A).obj Y) := by
  rw [← ModuleCat.lsmul_eq_smul_id]
  apply ModuleCat.hom_ext
  change (LinearMap.lsmul R Y r).baseChange A = LinearMap.lsmul A (A ⊗[R] Y) (algebraMap R A r)
  refine TensorProduct.AlgebraTensorModule.ext (R := R) (fun a y => ?_)
  change a ⊗ₜ[R] (r • y) = (algebraMap R A r) • (a ⊗ₜ[R] y)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]

variable [Module.Flat R A]

/-- The base change map is the scalar extension of the map on Ext induced by
the exact extension-of-scalars functor. -/
def baseChangeMap (X Y : ModuleCat.{u} R) (j : ℕ) :
    A ⊗[R] Ext X Y j →ₗ[A] Ext ((extend R A).obj X) ((extend R A).obj Y) j := by
  letI : Module R (Ext ((extend R A).obj X) ((extend R A).obj Y) j) :=
    Module.compHom _ (algebraMap R A)
  letI : IsScalarTower R A (Ext ((extend R A).obj X) ((extend R A).obj Y) j) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine LinearMap.liftBaseChange A
    { toFun := Ext.mapExactFunctor (extend R A)
      map_add' := Ext.mapExactFunctor_add (extend R A) X Y j
      map_smul' := ?_ }
  intro r e
  change (r • e).mapExactFunctor (extend R A) =
    (algebraMap R A r) • e.mapExactFunctor (extend R A)
  conv_lhs => rw [Ext.smul_eq_comp_mk₀]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, extend_map_smul_id,
    ← Ext.smul_eq_comp_mk₀]

@[simp]
lemma baseChangeMap_tmul (X Y : ModuleCat.{u} R) (j : ℕ) (a : A) (e : Ext X Y j) :
    baseChangeMap X Y j (a ⊗ₜ[R] e) = a • e.mapExactFunctor (extend R A) := rfl

/-- Ext over the original ring with a coefficient module over the extended
ring. The scalar action is transported by the derived tensor–Hom
adjunction, and is identified with postcomposition by multiplication. -/
def restrictedExt (X : ModuleCat.{u} R) (Z : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  letI := ((adjunction R A).extEquiv (X := X) (Y := Z) (n := n)).symm.module A
  ModuleCat.of A (Ext X ((restrict R A).obj Z) n)

/-- The derived tensor–Hom adjunction with its extended scalar action. -/
def extAdjunction (X : ModuleCat.{u} R) (Z : ModuleCat.{u} A) (n : ℕ) :
    Ext ((extend R A).obj X) Z n ≃ₗ[A] restrictedExt X Z n :=
  (((adjunction R A).extEquiv (X := X) (Y := Z) (n := n)).symm.linearEquiv A).symm

/-- The comparison with Ext into the scalar extension of the coefficient module. -/
def coefficientMap (X Y : ModuleCat.{u} R) (n : ℕ) :
    A ⊗[R] Ext X Y n →ₗ[A] restrictedExt X ((extend R A).obj Y) n :=
  (extAdjunction X ((extend R A).obj Y) n).toLinearMap ∘ₗ baseChangeMap X Y n

def RestrictedScalarAction : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (X : ModuleCat.{u} R) (Z : ModuleCat.{u} A) (n : ℕ) (a : A) (e : restrictedExt X Z n),
    (show Ext X ((restrict R A).obj Z) n from a • e) =
      (show Ext X ((restrict R A).obj Z) n from e).comp
        (Ext.mk₀ ((restrict R A).map (a • 𝟙 Z))) (add_zero n)

def CoefficientFormula : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (X Y : ModuleCat.{u} R) (n : ℕ) (a : A) (e : Ext X Y n),
    coefficientMap X Y n (a ⊗ₜ[R] e) =
      a • (show restrictedExt X ((extend R A).obj Y) n from
        e.comp (Ext.mk₀ ((adjunction R A).unit.app Y)) (add_zero n))

section Completion

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

abbrev completionRing := AdicCompletion (IsLocalRing.maximalIdeal R) R

/-- Maximal-ideal adic completion on modules and linear maps. -/
abbrev complete : ModuleCat.{u} R ⥤ ModuleCat.{u} (completionRing R) where
  obj X := ModuleCat.of _ (AdicCompletion (IsLocalRing.maximalIdeal R) X)
  map f := ModuleCat.ofHom (AdicCompletion.map (IsLocalRing.maximalIdeal R) f.hom)
  map_id X := ModuleCat.hom_ext (AdicCompletion.map_id _ X)
  map_comp f g := ModuleCat.hom_ext (AdicCompletion.map_comp _ f.hom g.hom).symm

/-- The canonical tensor formula for completion of a finite module. -/
def tensorCompletion (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    completionRing R ⊗[R] M ≃ₗ[completionRing R] AdicCompletion (IsLocalRing.maximalIdeal R) M :=
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (IsLocalRing.maximalIdeal R) M

def tensorCompletionIso (X : ModuleCat.{u} R) [Module.Finite R X] :
    (extend R (completionRing R)).obj X ≅ (complete R).obj X :=
  (tensorCompletion R X).toModuleIso

/-- Ext as a bifunctor, with the zero functor in negative degrees. -/
abbrev signedExt (B : Type u) [CommRing B] (j : ℤ) :
    (ModuleCat.{u} B)ᵒᵖ ⥤ ModuleCat.{u} B ⥤ ModuleCat.{u} B :=
  match j with
  | .ofNat n => linearExtFunctor B (ModuleCat.{u} B) n
  | .negSucc _ => (Functor.const _).obj ((Functor.const _).obj (ModuleCat.of B PUnit.{u+1}))

abbrev extModule (B : Type u) [CommRing B] (j : ℤ) (X Y : ModuleCat.{u} B) : ModuleCat.{u} B :=
  ((signedExt B j).obj (Opposite.op X)).obj Y

abbrev extPull {B : Type u} [CommRing B] {X X' : ModuleCat.{u} B}
    (f : X' ⟶ X) (Y : ModuleCat.{u} B) (j : ℤ) :
    extModule B j X Y ⟶ extModule B j X' Y :=
  ((signedExt B j).map f.op).app Y

abbrev extPush {B : Type u} [CommRing B] (X : ModuleCat.{u} B)
    {Y Y' : ModuleCat.{u} B} (g : Y ⟶ Y') (j : ℤ) :
    extModule B j X Y ⟶ extModule B j X Y' :=
  ((signedExt B j).obj (Opposite.op X)).map g

instance signedExt_finite (X Y : ModuleCat.{u} R) [Module.Finite R X]
    [Module.Finite R Y] (j : ℤ) : Module.Finite R (extModule R j X Y) := by
  cases j with
  | ofNat n => exact inferInstanceAs (Module.Finite R (Ext X Y n))
  | negSucc n => exact inferInstanceAs (Module.Finite R PUnit.{u+1})

/-- The change of arguments from tensor models to completed modules. -/
def extCompletionIso (X Y : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R Y] (j : ℤ) :
    extModule (completionRing R) j ((extend R (completionRing R)).obj X)
      ((extend R (completionRing R)).obj Y) ≅
    extModule (completionRing R) j ((complete R).obj X) ((complete R).obj Y) :=
  let E := signedExt (completionRing R) j
  ((E.mapIso (tensorCompletionIso R X).symm.op).app ((extend R (completionRing R)).obj Y)) ≪≫
    (E.obj (Opposite.op ((complete R).obj X))).mapIso (tensorCompletionIso R Y)

def signedBaseChangeMap (X Y : ModuleCat.{u} R) (j : ℤ) :
    completionRing R ⊗[R] extModule R j X Y →ₗ[completionRing R]
      extModule (completionRing R) j ((extend R (completionRing R)).obj X)
        ((extend R (completionRing R)).obj Y) :=
  match j with
  | .ofNat n => baseChangeMap X Y n
  | .negSucc _ => 0

/-- The canonical comparison from completed Ext to Ext of the completed modules. -/
def completionMap (X Y : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R Y] (j : ℤ) :
    (complete R).obj (extModule R j X Y) →ₗ[completionRing R]
      extModule (completionRing R) j ((complete R).obj X) ((complete R).obj Y) :=
  (extCompletionIso R X Y j).hom.hom ∘ₗ signedBaseChangeMap R X Y j ∘ₗ
    (tensorCompletion R (extModule R j X Y)).symm.toLinearMap

abbrev signedRestrictedExt (X : ModuleCat.{u} R) (Z : ModuleCat.{u} (completionRing R)) (j : ℤ) :
    ModuleCat.{u} (completionRing R) :=
  match j with
  | .ofNat n => restrictedExt X Z n
  | .negSucc _ => ModuleCat.of _ PUnit.{u+1}

/-- Adjunction in integer degrees, identified with the unique map of zero
modules in negative degrees. -/
def signedAdjunction (X : ModuleCat.{u} R) (Z : ModuleCat.{u} (completionRing R)) (j : ℤ) :
    extModule (completionRing R) j ((extend R (completionRing R)).obj X) Z ≃ₗ[completionRing R]
      signedRestrictedExt R X Z j :=
  match j with
  | .ofNat n => extAdjunction X Z n
  | .negSucc _ => LinearEquiv.refl _ _

def signedCoefficientMap (X Y : ModuleCat.{u} R) (j : ℤ) :
    completionRing R ⊗[R] extModule R j X Y →ₗ[completionRing R]
      signedRestrictedExt R X ((extend R (completionRing R)).obj Y) j :=
  (signedAdjunction R X ((extend R (completionRing R)).obj Y) j).toLinearMap ∘ₗ
    signedBaseChangeMap R X Y j

def restrictedPull (X X' : ModuleCat.{u} R) (f : X' ⟶ X)
    (Z : ModuleCat.{u} (completionRing R)) (j : ℤ) :
    signedRestrictedExt R X Z j ⟶ signedRestrictedExt R X' Z j :=
  ModuleCat.ofHom ((signedAdjunction R X' Z j).toLinearMap ∘ₗ
    (extPull ((extend R (completionRing R)).map f) Z j).hom ∘ₗ
    (signedAdjunction R X Z j).symm.toLinearMap)

def restrictedPush (X : ModuleCat.{u} R) {Z Z' : ModuleCat.{u} (completionRing R)}
    (g : Z ⟶ Z') (j : ℤ) :
    signedRestrictedExt R X Z j ⟶ signedRestrictedExt R X Z' j :=
  ModuleCat.ofHom ((signedAdjunction R X Z' j).toLinearMap ∘ₗ
    (extPush ((extend R (completionRing R)).obj X) g j).hom ∘ₗ
    (signedAdjunction R X Z j).symm.toLinearMap)

def CompletionComparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X Y : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R Y] (j : ℤ),
    Function.Bijective (completionMap R X Y j)

def CoefficientComparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X Y : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R Y] (j : ℤ),
    Function.Bijective (signedCoefficientMap R X Y j)

def CompletionNaturality : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X X' Y Y' : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R X']
    [Module.Finite R Y] [Module.Finite R Y'] (f : X' ⟶ X) (g : Y ⟶ Y') (j : ℤ),
    (ModuleCat.ofHom (completionMap R X Y j) ≫ extPull ((complete R).map f) ((complete R).obj Y) j =
      (complete R).map (extPull f Y j) ≫ ModuleCat.ofHom (completionMap R X' Y j)) ∧
    (ModuleCat.ofHom (completionMap R X Y j) ≫ extPush ((complete R).obj X) ((complete R).map g) j =
      (complete R).map (extPush X g j) ≫ ModuleCat.ofHom (completionMap R X Y' j))

def CoefficientNaturality : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X X' Y Y' : ModuleCat.{u} R) (f : X' ⟶ X) (g : Y ⟶ Y') (j : ℤ),
    let F := extend R (completionRing R)
    (ModuleCat.ofHom (signedCoefficientMap R X Y j) ≫ restrictedPull R X X' f (F.obj Y) j =
      F.map (extPull f Y j) ≫ ModuleCat.ofHom (signedCoefficientMap R X' Y j)) ∧
    (ModuleCat.ofHom (signedCoefficientMap R X Y j) ≫ restrictedPush R X (F.map g) j =
      F.map (extPush X g j) ≫ ModuleCat.ofHom (signedCoefficientMap R X Y' j))

def RestrictedExtMaps : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X X' : ModuleCat.{u} R) (Z Z' : ModuleCat.{u} (completionRing R))
    (f : X' ⟶ X) (g : Z ⟶ Z') (n : ℕ) (e : restrictedExt X Z n),
    (show Ext X' ((restrict R (completionRing R)).obj Z) n from
        restrictedPull R X X' f Z (.ofNat n) e) =
      (Ext.mk₀ f).comp (show Ext X ((restrict R (completionRing R)).obj Z) n from e)
        (zero_add n) ∧
    (show Ext X ((restrict R (completionRing R)).obj Z') n from
        restrictedPush R X g (.ofNat n) e) =
      (show Ext X ((restrict R (completionRing R)).obj Z) n from e).comp
        (Ext.mk₀ ((restrict R (completionRing R)).map g)) (add_zero n)

def CompletionAdjunctionCompatibility : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X Y : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R Y] (j : ℤ)
    (t : completionRing R ⊗[R] extModule R j X Y),
    signedAdjunction R X ((extend R (completionRing R)).obj Y) j
      ((extCompletionIso R X Y j).inv
        (completionMap R X Y j (tensorCompletion R (extModule R j X Y) t))) =
    signedCoefficientMap R X Y j t

end Completion

end

end CommutativeAlgebraNotes.CompletionOfFiniteExt
