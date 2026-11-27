import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedRestriction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CoinductionComplex
import Mathlib.CategoryTheory.Adjunction.Unique

/-! Coinduction, the linear Hom comparison, and evaluation on cochain complexes. -/

namespace DerivedFormalization

open CategoryTheory CochainComplex.HomComplex
open ModuleCat (coextendScalars)
open ModuleCat.CoextendScalars (equiv)

noncomputable section

universe v u w t

set_option linter.checkUnivs false

namespace Coinduction

open Specs.DerivedFormalization.CoinductionComplex
  (precompositionModule restrictedRegular)

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)

/-- Coinduction applied termwise in every integer degree. -/
abbrev coinduce : Comp.{max v w} A ⥤ Comp.{max v w} B :=
  Specs.DerivedFormalization.CoinductionComplex.coinduceValue f

/-- The cochain map given by evaluation at one in every degree. -/
abbrev evaluation (I : Comp.{max v w} A) :
    (restrictScalarsComplex f).obj ((coinduce f).obj I) ⟶ I :=
  Specs.DerivedFormalization.CoinductionComplex.evaluationValue f I

theorem evaluation_apply (I : Comp.{max v w} A) (n : ℤ) (z : ((coinduce f).obj I).X n) :
    (evaluation f I).f n z = (equiv f (I.X n) z) (1 : B) := rfl

theorem coinduce_smul_apply (I : Comp.{max v w} A) (n : ℤ)
    (z : ((coinduce f).obj I).X n) (b b' : B) :
    (equiv f (I.X n) (b • z)) b' = (equiv f (I.X n) z) (b * b') :=
  congrArg (fun x : B => equiv f (I.X n) z x) (mul_comm b' b)

/-- The signed Hom over the source ring with the scalar action from its argument. -/
abbrev restrictedHom (M : Comp.{max v w} B) (I : Comp.{max v w} A) : Comp.{max v w} B :=
  Specs.DerivedFormalization.CoinductionComplex.restrictedHomValue f M I

private def moduleHomEquiv (X : ModuleCat.{max v w} B) (Y : ModuleCat.{max v w} A) :
    letI := precompositionModule f X Y
    (X ⟶ (coextendScalars f).obj Y) ≃ₗ[B] ((restrictScalars f).obj X ⟶ Y) := by
  letI := precompositionModule f X Y
  refine { toAddEquiv := ((ModuleCat.restrictCoextendScalarsAdj.{v, u, w} f).homAddEquiv X Y).symm
           map_smul' := ?_ }
  intro b h
  apply ModuleCat.hom_ext
  ext x
  change (equiv f Y (b • h (x : X))) (1 : B) = (equiv f Y (h (b • (x : X)))) (1 : B)
  exact congrArg (fun z : (coextendScalars f).obj Y => (equiv f Y z) (1 : B))
    (h.hom.map_smul b (x : X)).symm

private def cochainEquiv (M : Comp.{max v w} B) (I : Comp.{max v w} A) (n : ℤ) :
    (internalHom M ((coinduce f).obj I)).X n ≃ₗ[B] (restrictedHom f M I).X n where
  toFun z := Cochain.mk fun i j h => moduleHomEquiv f (M.X i) (I.X j) (z.v i j h)
  invFun z := Cochain.mk fun i j h => (moduleHomEquiv f (M.X i) (I.X j)).symm (z.v i j h)
  left_inv _ := Cochain.ext _ _ fun i j _ => (moduleHomEquiv f (M.X i) (I.X j)).symm_apply_apply _
  right_inv _ := Cochain.ext _ _ fun i j _ => (moduleHomEquiv f (M.X i) (I.X j)).apply_symm_apply _
  map_add' _ _ := Cochain.ext _ _ fun i j _ => (moduleHomEquiv f (M.X i) (I.X j)).map_add _ _
  map_smul' _ _ := Cochain.ext _ _ fun i j _ => (moduleHomEquiv f (M.X i) (I.X j)).map_smul _ _

private theorem cochainEquiv_d (M : Comp.{max v w} B) (I : Comp.{max v w} A)
    (n m : ℤ) (z : (internalHom M ((coinduce f).obj I)).X n) :
    cochainEquiv f M I m ((internalHom M ((coinduce f).obj I)).d n m z) =
      (restrictedHom f M I).d n m (cochainEquiv f M I n z) := by
  apply Cochain.ext
  intro i j hij
  change moduleHomEquiv f (M.X i) (I.X j) ((δ n m z).v i j hij) =
    (δ n m (cochainEquiv f M I n z)).v i j hij
  simp only [δ, Cochain.mk_v, Functor.mapHomologicalComplex_obj_d, Units.smul_def]
  rfl

/-- The signed cochain Hom adjunction, linear over the target ring. -/
def homIso (M : Comp.{max v w} B) (I : Comp.{max v w} A) :
    internalHom M ((coinduce f).obj I) ≅ restrictedHom f M I :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainEquiv f M I n).toModuleIso)
    (fun n m _ => ModuleCat.hom_ext (LinearMap.ext fun z => (cochainEquiv_d f M I n m z).symm))

theorem homIso_hom_apply (M : Comp.{max v w} B) (I : Comp.{max v w} A) (n : ℤ)
    (z : (internalHom M ((coinduce f).obj I)).X n) (i j : ℤ) (h : i + n = j) (x : M.X i) :
    (show Cochain ((restrictScalarsComplex f).obj M) I n from (homIso f M I).hom.f n z).v i j h x =
      (equiv f (I.X j) (z.v i j h x)) (1 : B) := rfl

theorem homIso_inv_apply (M : Comp.{max v w} B) (I : Comp.{max v w} A) (n : ℤ)
    (z : (restrictedHom f M I).X n) (i j : ℤ) (h : i + n = j) (x : M.X i) (b : B) :
    (equiv f (I.X j) (((homIso f M I).inv.f n z).v i j h x)) b =
      (show Cochain ((restrictScalarsComplex f).obj M) I n from z).v i j h (b • x) := rfl

theorem homComparison : Specs.DerivedFormalization.CoinductionComplex.homComparison.{v, u, w} :=
  fun f M I => ⟨homIso f M I, homIso_hom_apply f M I, homIso_inv_apply f M I⟩

private theorem precomposition_restrict_smul (M : Comp.{max v w} B) (I : Comp.{max v w} A)
    (n : ℤ) (a : A) (z : (restrictedHom f M I).X n) :
    (show Cochain ((restrictScalarsComplex f).obj M) I n from f a • z) =
      a • (show Cochain ((restrictScalarsComplex f).obj M) I n from z) := by
  apply Cochain.ext
  intro i j h
  apply ModuleCat.hom_ext
  ext x
  change (z.v i j h) (a • x) = a • (z.v i j h) x
  exact (z.v i j h).hom.map_smul a x

/-- Restricting the scalars of the comparison's target gives the ordinary signed Hom. -/
def restrictedHomForgetIso (M : Comp.{max v w} B) (I : Comp.{max v w} A) :
    (restrictScalarsComplex f).obj (restrictedHom f M I) ≅
      internalHom ((restrictScalarsComplex f).obj M) I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      (show ((restrictScalarsComplex f).obj (restrictedHom f M I)).X n ≃ₗ[A]
        (internalHom ((restrictScalarsComplex f).obj M) I).X n from
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := precomposition_restrict_smul f M I n }).toModuleIso)
    (fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

theorem forgetHomComparison :
    Specs.DerivedFormalization.CoinductionComplex.forgetHomComparison.{v, u, w} :=
  fun f M I => ⟨restrictedHomForgetIso f M I, fun _ _ => rfl⟩

/-- The cochain Hom adjunction after restricting the scalars on the source. -/
def underlyingHomIso (M : Comp.{max v w} B) (I : Comp.{max v w} A) :
    (restrictScalarsComplex f).obj (internalHom M ((coinduce f).obj I)) ≅
      internalHom ((restrictScalarsComplex f).obj M) I :=
  (restrictScalarsComplex f).mapIso (homIso f M I) ≪≫ restrictedHomForgetIso f M I

theorem underlyingHomIso_apply (M : Comp.{max v w} B) (I : Comp.{max v w} A)
    (n : ℤ) (z : (internalHom M ((coinduce f).obj I)).X n) (i j : ℤ) (h : i + n = j)
    (x : M.X i) :
    ((underlyingHomIso f M I).hom.f n z).v i j h x =
      (equiv f (I.X j) (z.v i j h x)) (1 : B) := rfl

theorem underlyingHomIso_natural {M M' : Comp.{max v w} B} {I I' : Comp.{max v w} A}
    (a : M' ⟶ M) (b : I ⟶ I') :
    (restrictScalarsComplex f).map (internalHomMap a ((coinduce f).map b)) ≫
        (underlyingHomIso f M' I').hom =
      (underlyingHomIso f M I).hom ≫ internalHomMap ((restrictScalarsComplex f).map a) b := by
  ext n : 1
  apply ModuleCat.hom_ext
  ext z : 1
  apply Cochain.ext
  intro i j h
  apply ModuleCat.hom_ext
  ext x
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, internalHomMap_apply]
  let z₀ : Cochain M ((coinduce f).obj I) n := z
  let x₀ : M'.X i := x
  change (equiv f (I'.X j)
    (((internalHomMap a ((coinduce f).map b)).f n z₀).v i j h x₀)) (1 : B) =
      b.f j ((equiv f (I.X j) (z₀.v i j h (a.f i x₀))) (1 : B))
  rw [internalHomMap_apply a ((coinduce f).map b) h z₀ x₀]
  rfl

theorem homNaturality : Specs.DerivedFormalization.CoinductionComplex.homNaturality.{v, u, w} :=
  fun f => ⟨underlyingHomIso.{v} f, underlyingHomIso_apply.{v} f, underlyingHomIso_natural.{v} f⟩

/-- Coinduction sends K-injective complexes to K-injective complexes. -/
theorem isKInjective_coinduce (I : Comp.{max v w} A) (hI : IsKInjective I) :
    IsKInjective ((coinduce f).obj I) := by
  apply (isKInjective_iff_internalHom_acyclic _).2
  intro M hM
  have hrM : ((restrictScalarsComplex f).obj M).Acyclic := by
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((restrictScalars f).map_isZero ((hM n).isZero_homology)).of_iso
      ((restrictScalarsCohomologyIso f n).app M)
  have hHom := (isKInjective_iff_internalHom_acyclic I).1 hI _ hrM
  intro n
  apply HomologicalComplex.ExactAt.of_iso (e := (homIso f M I).symm)
  have h := hHom n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at h ⊢
  exact h

private def liftedRegularEquiv :
    ((ModuleCat.restrictScalars.{w} f).obj (ModuleCat.of B B)) ≃ₗ[A] restrictedRegular.{v} f where
  toFun := ULift.up
  invFun := ULift.down
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private def restrictedCoinducedTermEquiv (Y : ModuleCat.{max v w} A) :
    (restrictScalars f).obj ((coextendScalars f).obj Y) ≃ₗ[A]
      ((ModuleCat.restrictScalars.{w} f).obj (ModuleCat.of B B) →ₗ[A] Y) where
  toAddEquiv := (equiv f Y).toAddEquiv
  map_smul' a z := by
    ext b
    change (equiv f Y z) ((show B from b) * f a) = a • (equiv f Y z) b
    rw [mul_comm]
    exact (equiv f Y z).map_smul a b

private def stalkEquiv (I : Comp.{max v w} A) (n : ℤ) :
    (internalHom ((stalk A).obj (restrictedRegular.{v} f)) I).X n ≃ₗ[A]
      ((restrictScalarsComplex f).obj ((coinduce f).obj I)).X n :=
  (Cochain.fromSingleLinearEquiv (zero_add n)).trans
    (ModuleCat.homLinearEquiv.trans
      ((LinearEquiv.arrowCongr (liftedRegularEquiv.{v} f).symm (LinearEquiv.refl A (I.X n))).trans
        (restrictedCoinducedTermEquiv f (I.X n)).symm))

private theorem stalkEquiv_d (I : Comp.{max v w} A) (n m : ℤ)
    (z : (internalHom ((stalk A).obj (restrictedRegular.{v} f)) I).X n) :
    stalkEquiv f I m ((internalHom ((stalk A).obj (restrictedRegular.{v} f)) I).d n m z) =
      ((restrictScalarsComplex f).obj ((coinduce f).obj I)).d n m (stalkEquiv f I n z) := by
  obtain ⟨φ, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  change stalkEquiv f I m (δ n m (Cochain.fromSingleMk φ (zero_add n))) = _
  rw [Cochain.δ_fromSingleMk φ (zero_add n) m m (zero_add m)]
  apply ModuleCat.CoextendScalars.ext
  ext b
  simp [stalkEquiv, Cochain.fromSingleLinearEquiv, Cochain.fromSingleEquiv_fromSingleMk,
    restrictedCoinducedTermEquiv]
  rfl

/-- The underlying coinduced complex is the signed Hom from the regular module in degree zero. -/
def stalkIso (I : Comp.{max v w} A) :
    internalHom ((stalk A).obj (restrictedRegular.{v} f)) I ≅
      (restrictScalarsComplex f).obj ((coinduce f).obj I) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (stalkEquiv f I n).toModuleIso)
    (fun n m _ => ModuleCat.hom_ext (LinearMap.ext fun z => (stalkEquiv_d f I n m z).symm))

theorem stalkComparison : Specs.DerivedFormalization.CoinductionComplex.stalkComparison.{v, u, w} :=
  fun f I => ⟨stalkIso f I, fun _ _ _ => rfl⟩

section Composition

variable {C : Type t} [CommRing C] (g : B →+* C)

private abbrev compositeAdjunction :
    restrictScalars.{max v w t} (g.comp f) ⊣
      coextendScalars.{u, w, max v w t} f ⋙ coextendScalars.{w, t, max v w t} g :=
  ((ModuleCat.restrictCoextendScalarsAdj.{max v w t} g).comp
    (ModuleCat.restrictCoextendScalarsAdj.{max v w t} f)).ofNatIsoLeft
      (ModuleCat.restrictScalarsComp f g).symm

private def moduleCompositionIso :
    coextendScalars.{u, w, max v w t} f ⋙ coextendScalars.{w, t, max v w t} g ≅
      coextendScalars.{u, t, max v w t} (g.comp f) :=
  (compositeAdjunction.{v} f g).rightAdjointUniq
    (ModuleCat.restrictCoextendScalarsAdj.{max v w t} (g.comp f))

private theorem moduleCompositionIso_one (Y : ModuleCat.{max v w t} A)
    (z : ((coextendScalars f ⋙ coextendScalars g).obj Y)) :
    (equiv (g.comp f) Y ((moduleCompositionIso.{v} f g).hom.app Y z)) (1 : C) =
      (equiv f Y ((equiv g ((coextendScalars f).obj Y) z) (1 : C))) (1 : B) := by
  have h := (compositeAdjunction.{v} f g).rightAdjointUniq_hom_app_counit
    (ModuleCat.restrictCoextendScalarsAdj.{max v w t} (g.comp f)) Y
  rw [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_counit_app] at h
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z

private theorem moduleCompositionIso_apply (Y : ModuleCat.{max v w t} A)
    (z : ((coextendScalars f ⋙ coextendScalars g).obj Y)) (c : C) :
    (equiv (g.comp f) Y ((moduleCompositionIso.{v} f g).hom.app Y z)) c =
      (equiv f Y ((equiv g ((coextendScalars f).obj Y) z) c)) (1 : B) := by
  have h := moduleCompositionIso_one.{v} f g Y (c • z)
  rw [((moduleCompositionIso.{v} f g).hom.app Y).hom.map_smul] at h
  change (equiv (g.comp f) Y ((moduleCompositionIso.{v} f g).hom.app Y z)) (1 * c : C) =
    (equiv f Y ((equiv g ((coextendScalars f).obj Y) z) (1 * c : C))) (1 : B) at h
  simpa only [one_mul] using h

/-- Coinduction for a composite is naturally isomorphic to successive coinduction. -/
def compositionIso :
    coinduce.{max v w t} f ⋙ coinduce.{max v w t} g ≅ coinduce.{max v w t} (g.comp f) := by
  letI := (ModuleCat.restrictCoextendScalarsAdj.{max v w t} f).right_adjoint_additive
  letI := (ModuleCat.restrictCoextendScalarsAdj.{max v w t} g).right_adjoint_additive
  letI := (ModuleCat.restrictCoextendScalarsAdj.{max v w t} (g.comp f)).right_adjoint_additive
  exact Functor.mapHomologicalComplexCompIso (moduleCompositionIso.{v} f g) (.up ℤ)

theorem compositionIso_apply (I : Comp.{max v w t} A) (n : ℤ)
    (z : ((coinduce.{max v w t} f ⋙ coinduce.{max v w t} g).obj I).X n) (c : C) :
    (equiv (g.comp f) (I.X n) (((compositionIso.{v} f g).hom.app I).f n z)) c =
      (equiv f (I.X n)
        ((equiv g (((coinduce.{max v w t} f).obj I).X n) z) c)) (1 : B) :=
  moduleCompositionIso_apply.{v} f g (I.X n) z c

theorem composition_evaluation (I : Comp.{max v w t} A) :
    (restrictScalarsComplex (g.comp f)).map ((compositionIso.{v} f g).hom.app I) ≫
        evaluation.{max v w t} (g.comp f) I =
      (Specs.DerivedFormalization.CoinductionComplex.restrictionComp.{v} f g).hom.app
        ((coinduce.{max v w t} g).obj ((coinduce.{max v w t} f).obj I)) ≫
        (restrictScalarsComplex f).map
          (evaluation.{max v w t} g ((coinduce.{max v w t} f).obj I)) ≫
          evaluation.{max v w t} f I := by
  ext n : 1
  apply ModuleCat.hom_ext
  ext z
  exact compositionIso_apply.{v} f g I n z 1

theorem composition : Specs.DerivedFormalization.CoinductionComplex.composition.{v, u, w, t} :=
  fun f g => ⟨compositionIso.{v} f g, compositionIso_apply.{v} f g, composition_evaluation.{v} f g⟩

end Composition

end Coinduction

end

end DerivedFormalization
