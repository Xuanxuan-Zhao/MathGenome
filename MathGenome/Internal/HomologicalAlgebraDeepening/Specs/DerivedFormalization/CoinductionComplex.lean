import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedRestriction
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Adjunction.Additive

/-! Coinduction on arbitrary unbounded cochain complexes. -/

namespace Specs.DerivedFormalization.CoinductionComplex

open CategoryTheory CochainComplex.HomComplex
open Cochains (compValue stalkValue)
open CochainModels (internalHomValue internalHomMapValue isKInjectiveValue)
open DerivedRestriction (restrictScalarsValue restrictScalarsComplexValue)

noncomputable section

set_option linter.checkUnivs false

universe v u w t

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)

/-- Coinduction in each degree via the module functor `Hom_A(B, -)`. -/
def coinduceValue : compValue.{max v w} A ⥤ compValue.{max v w} B :=
  letI := (ModuleCat.restrictCoextendScalarsAdj.{v, u, w} f).right_adjoint_additive
  (ModuleCat.coextendScalars.{u, w, max v w} f).mapHomologicalComplex (.up ℤ)

def coinduceType :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (_ : A →+* B),
    compValue.{max v w} A ⥤ compValue.{max v w} B

/-- Evaluation at one on each term of the restricted coinduced complex. -/
def evaluationValue (I : compValue.{max v w} A) :
    (restrictScalarsComplexValue f).obj ((coinduceValue f).obj I) ⟶ I :=
  letI := (ModuleCat.restrictCoextendScalarsAdj.{v, u, w} f).right_adjoint_additive
  (NatTrans.mapHomologicalComplex
    (ModuleCat.restrictCoextendScalarsAdj.{v, u, w} f).counit (.up ℤ)).app I

def evaluationType :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (I : compValue.{max v w} A),
    (restrictScalarsComplexValue f).obj ((coinduceValue f).obj I) ⟶ I

def evaluationFormula : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (I : compValue.{max v w} A) (n : ℤ) (z : ((coinduceValue f).obj I).X n),
    (evaluationValue f I).f n z =
      (ModuleCat.CoextendScalars.equiv f (I.X n) z) (1 : B)

def scalarFormula : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (I : compValue.{max v w} A) (n : ℤ) (z : ((coinduceValue f).obj I).X n) (b b' : B),
    (ModuleCat.CoextendScalars.equiv f (I.X n) (b • z)) b' =
      (ModuleCat.CoextendScalars.equiv f (I.X n) z) (b * b')

/-- Scalars on a restricted Hom act by precomposition on its B-module argument. -/
@[instance_reducible]
def precompositionModule (X : ModuleCat.{max v w} B) (Y : ModuleCat.{max v w} A) :
    Module B ((restrictScalarsValue f).obj X ⟶ Y) where
  smul b h := (restrictScalarsValue f).map (b • 𝟙 X) ≫ h
  one_smul h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((1 : B) • (x : X)) = h x
    rw [one_smul]
  mul_smul b c h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((b * c) • (x : X)) = h (c • (b • (x : X)))
    rw [mul_comm, mul_smul]
  smul_zero b := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  smul_add b g h := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  add_smul b c h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((b + c) • (x : X)) = h (b • (x : X)) + h (c • (x : X))
    rw [add_smul, map_add]
  zero_smul h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((0 : B) • (x : X)) = 0
    rw [zero_smul]
    exact h.hom.map_zero

@[instance_reducible]
def precompositionCochainModule (M : compValue.{max v w} B) (I : compValue.{max v w} A)
    (n : ℤ) : Module B (Cochain ((restrictScalarsComplexValue f).obj M) I n) :=
  @Pi.module (Triplet n) (fun T => ((restrictScalarsComplexValue f).obj M).X T.p ⟶ I.X T.q)
    B _ (fun _ => inferInstance) (fun T => precompositionModule f (M.X T.p) (I.X T.q))

theorem precomposition_smul_v (M : compValue.{max v w} B) (I : compValue.{max v w} A)
    (n : ℤ) (b : B) (z : Cochain ((restrictScalarsComplexValue f).obj M) I n)
    (i j : ℤ) (h : i + n = j) :
    (@SMul.smul B _ (precompositionCochainModule f M I n).toSMul b z).v i j h =
      (restrictScalarsValue f).map (b • 𝟙 (M.X i)) ≫ z.v i j h := rfl

private theorem differential_smul (M : compValue.{max v w} B) (I : compValue.{max v w} A)
    (n m : ℤ) (b : B) (z : Cochain ((restrictScalarsComplexValue f).obj M) I n) :
    δ n m (@SMul.smul B _ (precompositionCochainModule f M I n).toSMul b z) =
      @SMul.smul B _ (precompositionCochainModule f M I m).toSMul b (δ n m z) := by
  have comm (i j : ℤ) :
      (restrictScalarsValue f).map (M.d i j) ≫ (restrictScalarsValue f).map (b • 𝟙 (M.X j)) =
        (restrictScalarsValue f).map (b • 𝟙 (M.X i)) ≫ (restrictScalarsValue f).map (M.d i j) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]
  apply Cochain.ext
  intro i j h
  rw [precomposition_smul_v]

  simp only [δ, Cochain.mk_v, Functor.mapHomologicalComplex_obj_d,
    Preadditive.comp_add, Linear.comp_units_smul]
  rw [precomposition_smul_v f M I n b z, precomposition_smul_v f M I n b z]
  simp only [Category.assoc]
  rw [← Category.assoc ((ModuleCat.restrictScalars f).map (M.d i _)), comm, Category.assoc]

private def restrictedHomTerm (M : compValue.{max v w} B) (I : compValue.{max v w} A)
    (n : ℤ) : ModuleCat.{max v w} B :=
  letI := precompositionCochainModule f M I n
  ModuleCat.of B (Cochain ((restrictScalarsComplexValue f).obj M) I n)

/-- The ordinary signed Hom over A, with the B-module action on the argument. -/
def restrictedHomValue (M : compValue.{max v w} B) (I : compValue.{max v w} A) :
    compValue.{max v w} B where
  X := restrictedHomTerm f M I
  d n m := ModuleCat.ofHom (X := restrictedHomTerm f M I n) (Y := restrictedHomTerm f M I m)
    { toFun := δ n m
      map_add' := δ_add n m
      map_smul' := differential_smul f M I n m }
  shape n m h := ModuleCat.hom_ext (LinearMap.ext fun z => δ_shape n m h z)
  d_comp_d' n m l _ _ := ModuleCat.hom_ext (LinearMap.ext fun z => δ_δ n m l z)

def restrictedHomType :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (_ : A →+* B)
    (_ : compValue.{max v w} B) (_ : compValue.{max v w} A), compValue.{max v w} B

def homComparison : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (M : compValue.{max v w} B) (I : compValue.{max v w} A),
    ∃ e : internalHomValue M ((coinduceValue f).obj I) ≅ restrictedHomValue f M I,
      (∀ (n : ℤ) (z : (internalHomValue M ((coinduceValue f).obj I)).X n)
          (i j : ℤ) (h : i + n = j) (x : M.X i),
        ((show Cochain ((restrictScalarsComplexValue f).obj M) I n from e.hom.f n z).v i j h) x =
          (ModuleCat.CoextendScalars.equiv f (I.X j) (z.v i j h x)) (1 : B)) ∧
      (∀ (n : ℤ) (z : (restrictedHomValue f M I).X n)
          (i j : ℤ) (h : i + n = j) (x : M.X i) (b : B),
        (ModuleCat.CoextendScalars.equiv f (I.X j) ((e.inv.f n z).v i j h x)) b =
          (show Cochain ((restrictScalarsComplexValue f).obj M) I n from z).v i j h (b • x))

def forgetHomComparison : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (M : compValue.{max v w} B) (I : compValue.{max v w} A),
    ∃ e : (restrictScalarsComplexValue f).obj (restrictedHomValue f M I) ≅
          internalHomValue ((restrictScalarsComplexValue f).obj M) I,
      ∀ (n : ℤ) (z : (restrictedHomValue f M I).X n),
        e.hom.f n z = (show Cochain ((restrictScalarsComplexValue f).obj M) I n from z)

def homNaturality : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B),
    let F := restrictScalarsComplexValue.{max v w} f
    let G := coinduceValue.{v} f
    ∃ e : ∀ (M : compValue.{max v w} B) (I : compValue.{max v w} A),
        F.obj (internalHomValue M (G.obj I)) ≅ internalHomValue (F.obj M) I,
      (∀ (M : compValue.{max v w} B) (I : compValue.{max v w} A) (n : ℤ)
          (z : (internalHomValue M (G.obj I)).X n) (i j : ℤ) (h : i + n = j) (x : M.X i),
        ((e M I).hom.f n z).v i j h x =
          (ModuleCat.CoextendScalars.equiv f (I.X j) (z.v i j h x)) (1 : B)) ∧
      (∀ {M M' : compValue.{max v w} B} {I I' : compValue.{max v w} A}
          (a : M' ⟶ M) (b : I ⟶ I'),
        F.map (internalHomMapValue a (G.map b)) ≫ (e M' I').hom =
          (e M I).hom ≫ internalHomMapValue (F.map a) b)

def isKInjectiveCoinduce : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (I : compValue.{max v w} A),
    isKInjectiveValue I → isKInjectiveValue ((coinduceValue f).obj I)

/-- The regular module, lifted to the universe of the complex terms. -/
abbrev restrictedRegular : ModuleCat.{max v w} A :=
  (restrictScalarsValue.{max v w} f).obj (ModuleCat.of B (ULift.{v} B))

def stalkComparison : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (I : compValue.{max v w} A),
    let T := restrictedRegular.{v} f
    ∃ e : internalHomValue ((stalkValue A).obj T) I ≅
          (restrictScalarsComplexValue f).obj ((coinduceValue f).obj I),
      ∀ (n : ℤ) (z : (internalHomValue ((stalkValue A).obj T) I).X n)
          (b : B),
        (ModuleCat.CoextendScalars.equiv f (I.X n) (e.hom.f n z)) b =
          z.v 0 n (zero_add n) ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv (ULift.up b))

variable {C : Type t} [CommRing C] (g : B →+* C)

/-- Compare restriction along a composite to the two successive restrictions. -/
abbrev restrictionComp :
    restrictScalarsComplexValue.{max v w t} (g.comp f) ≅
      restrictScalarsComplexValue g ⋙ restrictScalarsComplexValue f :=
  NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsComp f g) (.up ℤ)

def composition : Prop :=
  ∀ {A : Type u} {B : Type w} {C : Type t} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C),
    ∃ e : coinduceValue.{max v w t} f ⋙ coinduceValue.{max v w t} g ≅ coinduceValue.{max v w t} (g.comp f),
      (∀ (I : compValue.{max v w t} A) (n : ℤ)
          (z : (((coinduceValue.{max v w t} f ⋙ coinduceValue.{max v w t} g).obj I)).X n) (c : C),
        (ModuleCat.CoextendScalars.equiv (g.comp f) (I.X n) ((e.hom.app I).f n z)) c =
          (ModuleCat.CoextendScalars.equiv f (I.X n)
            ((ModuleCat.CoextendScalars.equiv g (((coinduceValue.{max v w t} f).obj I).X n) z) c)) (1 : B)) ∧
      (∀ I : compValue.{max v w t} A,
        (restrictScalarsComplexValue (g.comp f)).map (e.hom.app I) ≫
            evaluationValue.{max v w t} (g.comp f) I =
          ((restrictionComp.{v} f g).hom.app ((coinduceValue.{max v w t} g).obj ((coinduceValue.{max v w t} f).obj I))) ≫
            (restrictScalarsComplexValue f).map (evaluationValue.{max v w t} g ((coinduceValue.{max v w t} f).obj I)) ≫
            evaluationValue.{max v w t} f I)

end

end Specs.DerivedFormalization.CoinductionComplex
