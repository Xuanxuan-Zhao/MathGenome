import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Basic
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift

/-! The ordinary signed tensor at an independent module universe and its comparisons. -/

namespace Specs.DerivedFormalization.CochainTensor

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
open Cochains (compValue)
open CochainCoefficientLift (lift termEquiv)
open CochainModels (internalHomValue internalHomMapValue)
open CochainComplex.HomComplex (Cochain)

universe u v t

set_option linter.checkUnivs false

variable {R : Type u} [CommRing R]

noncomputable section

abbrev tensor (X Y : compValue.{v} R) : compValue.{v} R :=
  DG.Basic.cochainTensor X Y

def TensorType := ∀ {R : Type u} [CommRing R], compValue.{v} R → compValue.{v} R → compValue.{v} R

def map {X X' Y Y' : compValue.{v} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensor X Y ⟶ tensor X' Y' :=
  mapBifunctorMap f g (DG.Basic.moduleTensor R) (.up ℤ)

def MapType :=
  ∀ {R : Type u} [CommRing R] {X X' Y Y' : compValue.{v} R} (_ : X ⟶ X') (_ : Y ⟶ Y'),
    tensor X Y ⟶ tensor X' Y'

abbrev ι (X Y : compValue.{v} R) (i j n : ℤ) (h : i + j = n) :=
  DG.Basic.cochainTensorInclusion X Y i j n h

def InclusionType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (i j n : ℤ) (_ : i + j = n),
    ModuleCat.of R (X.X i ⊗[R] Y.X j) ⟶ (tensor X Y).X n

abbrev pure (X Y : compValue.{v} R) {i j n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (tensor X Y).X n := ι X Y i j n h (x ⊗ₜ[R] y)

def cofan (X Y : compValue.{v} R) (n : ℤ) :
    Cofan (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ModuleCat.of R (X.X p.1.1 ⊗[R] Y.X p.1.2)) :=
  Cofan.mk ((tensor X Y).X n) (fun p => ι X Y p.1.1 p.1.2 n p.2)

def isKFlat (F : compValue.{v} R) : Prop :=
  ∀ E : compValue.{v} R, E.Acyclic → (tensor E F).Acyclic

def KFlatType := ∀ {R : Type u} [CommRing R], compValue.{v} R → Prop

def Coproduct : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (n : ℤ),
    Nonempty (IsColimit (cofan X Y n))

def Differential : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (i j n : ℤ) (h : i + j = n)
    (x : X.X i) (y : Y.X j),
    (tensor X Y).d n (n + 1) (pure X Y h x y) =
      pure X Y (i := i + 1) (by omega : i + 1 + j = n + 1) (X.d i (i + 1) x) y +
        i.negOnePow • pure X Y (by omega : i + (j + 1) = n + 1) x (Y.d j (j + 1) y)

def DifferentialSquared : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (i j k : ℤ),
    (tensor X Y).d i j ≫ (tensor X Y).d j k = 0

def MapOnPure : Prop :=
  ∀ {R : Type u} [CommRing R] {X X' Y Y' : compValue.{v} R} (f : X ⟶ X') (g : Y ⟶ Y')
    (i j n : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
    (map f g).f n (pure X Y h x y) = pure X' Y' h (f.f i x) (g.f j y)

def HomotopyCompatibility : Prop :=
  ∀ {R : Type u} [CommRing R] {X X' Y Y' : compValue.{v} R} {f f' : X ⟶ X'} {g g' : Y ⟶ Y'},
    Homotopy f f' → Homotopy g g' → Nonempty (Homotopy (map f g) (map f' g'))

def Symmetry : Prop :=
  ∀ {R : Type u} [CommRing R],
    ∃ e : ∀ X Y : compValue.{v} R, tensor X Y ≅ tensor Y X,
      (∀ X Y (i j n : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
        (e X Y).hom.f n (pure X Y h x y) =
          (i * j).negOnePow • pure Y X (by omega : j + i = n) y x) ∧
      (∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
        map f g ≫ (e X' Y').hom = (e X Y).hom ≫ map g f) ∧
      ∀ X Y, (e X Y).hom ≫ (e Y X).hom = 𝟙 (tensor X Y)

def Diagonal : Prop :=
  ∀ {R : Type u} [CommRing R],
    ∃ e : ∀ X Y : compValue.{u} R, tensor X Y ≅ CochainModels.tensorComplexValue X Y,
      (∀ X Y (i j n : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
        (e X Y).hom.f n (pure X Y h x y) = ιTensorObj X Y i j n h (x ⊗ₜ[R] y)) ∧
      ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
        map f g ≫ (e X' Y').hom = (e X Y).hom ≫ CochainModels.tensorMapValue f g

def DiagonalKFlat : Prop :=
  ∀ {R : Type u} [CommRing R] (F : compValue.{u} R),
    isKFlat F ↔ CochainModels.isKFlatValue F

def LiftTensor : Prop :=
  ∀ {R : Type u} [CommRing R],
    ∃ e : ∀ X Y : compValue.{v} R,
      (lift.{t} R).obj (tensor X Y) ≅ tensor ((lift.{t} R).obj X) ((lift.{t} R).obj Y),
      (∀ X Y (i j n : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
        (e X Y).hom.f n (termEquiv.{t} (tensor X Y) n (pure X Y h x y)) =
          pure _ _ h (termEquiv.{t} X i x) (termEquiv.{t} Y j y)) ∧
      ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
        (lift.{t} R).map (map f g) ≫ (e X' Y').hom =
          (e X Y).hom ≫ map ((lift.{t} R).map f) ((lift.{t} R).map g)

def LiftHom : Prop :=
  ∀ {R : Type u} [CommRing R],
    ∃ e : ∀ X Y : compValue.{v} R,
      (lift.{t} R).obj (internalHomValue X Y) ≅
        internalHomValue ((lift.{t} R).obj X) ((lift.{t} R).obj Y),
      (∀ (X Y : compValue.{v} R) (q i j : ℤ) (h : i + q = j) (f : Cochain X Y q) (x : X.X i),
        ((e X Y).hom.f q (termEquiv.{t} (internalHomValue X Y) q f)).v i j h
            (termEquiv.{t} X i x) = termEquiv.{t} Y j (f.v i j h x)) ∧
      ∀ {X X' Y Y'} (f : X' ⟶ X) (g : Y ⟶ Y'),
        (lift.{t} R).map (internalHomMapValue f g) ≫ (e X' Y').hom =
          (e X Y).hom ≫ internalHomMapValue ((lift.{t} R).map f) ((lift.{t} R).map g)

end

end Specs.DerivedFormalization.CochainTensor
