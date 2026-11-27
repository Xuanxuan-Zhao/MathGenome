import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! Specifications for the signed tensor, internal Hom, and K-acyclicity tests. -/

namespace Specs.DerivedFormalization.CochainModels

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory TensorProduct ZeroObject
open CochainComplex (linearHomComplex)
open CochainComplex.HomComplex
open HomologicalComplex (ιTensorObj)
open Specs.DerivedFormalization.Cochains (compValue)

universe u v

set_option linter.checkUnivs false
set_option linter.unusedVariables false

variable {R : Type u} [CommRing R]

def tensorComplexType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{u} R), compValue.{u} R

noncomputable abbrev tensorComplexValue (X Y : compValue.{u} R) : compValue.{u} R :=
  HomologicalComplex.tensorObj X Y

def tensorMapType :=
  ∀ {R : Type u} [CommRing R] {X X' Y Y' : compValue.{u} R} (f : X ⟶ X') (g : Y ⟶ Y'),
      tensorComplexValue X Y ⟶ tensorComplexValue X' Y'

noncomputable abbrev tensorMapValue {X X' Y Y' : compValue.{u} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorComplexValue X Y ⟶ tensorComplexValue X' Y' :=
  HomologicalComplex.tensorHom f g

def internalHomType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R), compValue.{v} R

abbrev internalHomValue (X Y : compValue.{v} R) : compValue.{v} R :=
  linearHomComplex R X Y

def isKFlatType :=
  ∀ {R : Type u} [CommRing R] (F : compValue.{u} R), Prop

def isKFlatValue (F : compValue.{u} R) : Prop :=
  ∀ E : compValue.{u} R, E.Acyclic → (tensorComplexValue E F).Acyclic

def isKProjectiveType :=
  ∀ {R : Type u} [CommRing R] (P : compValue.{v} R), Prop

abbrev isKProjectiveValue (P : compValue.{v} R) : Prop := CochainComplex.IsKProjective P

def isKInjectiveType :=
  ∀ {R : Type u} [CommRing R] (I : compValue.{v} R), Prop

abbrev isKInjectiveValue (I : compValue.{v} R) : Prop := CochainComplex.IsKInjective I

def internalHomMapType :=
  ∀ {R : Type u} [CommRing R] {A A' B B' : compValue.{v} R} (g : A' ⟶ A) (h : B ⟶ B'),
      linearHomComplex R A B ⟶ linearHomComplex R A' B'

def internalHomMapValue {A A' B B' : compValue.{v} R} (g : A' ⟶ A) (h : B ⟶ B') :
    linearHomComplex R A B ⟶ linearHomComplex R A' B' where
  f n := ModuleCat.ofHom
    { toFun := fun f => ((Cochain.ofHom g).comp f (zero_add n)).comp
        (Cochain.ofHom h) (add_zero n)
      map_add' := by intros; simp [Cochain.comp_add]
      map_smul' := by intros; simp [Cochain.comp_smul] }
  comm' := by
    intro n m _
    apply ModuleCat.hom_ext
    ext f : 1
    change δ n m (((Cochain.ofHom g).comp f (zero_add n)).comp (Cochain.ofHom h) (add_zero n)) =
      ((Cochain.ofHom g).comp (δ n m f) (zero_add m)).comp (Cochain.ofHom h) (add_zero m)
    simp

def tensorCofanType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{u} R) (n : ℤ),
      Cofan (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} => X.X p.1.1 ⊗ Y.X p.1.2)

noncomputable def tensorCofanValue (X Y : compValue.{u} R) (n : ℤ) :
    Cofan (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} => X.X p.1.1 ⊗ Y.X p.1.2) :=
  Cofan.mk ((tensorComplexValue X Y).X n) (fun p => ιTensorObj X Y p.1.1 p.1.2 n p.2)

def internalHomProductType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (n : ℤ),
      (internalHomValue X Y).X n ≃ₗ[R] (∀ i : ℤ, X.X i →ₗ[R] Y.X (i + n))

def internalHomProductValue (X Y : compValue.{v} R) (n : ℤ) :
    (internalHomValue X Y).X n ≃ₗ[R] (∀ i : ℤ, X.X i →ₗ[R] Y.X (i + n)) where
  toFun f i := (f.v i (i + n) rfl).hom
  invFun f := Cochain.mk fun i j h => h ▸ ModuleCat.ofHom (f i)
  left_inv f := by
    apply Cochain.ext
    rintro i j rfl
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def internalHomCyclesZeroType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R), (X ⟶ Y) ≃ₗ[R] Cocycle X Y 0

def internalHomCyclesZeroValue (X Y : compValue.{v} R) : (X ⟶ Y) ≃ₗ[R] Cocycle X Y 0 :=
  (Cocycle.equivHom X Y).toLinearEquiv (by simp)

def internalHomCyclesShiftType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (n : ℤ), (X ⟶ Y⟦n⟧) ≃ₗ[R] Cocycle X Y n

def internalHomCyclesShiftValue (X Y : compValue.{v} R) (n : ℤ) :
    (X ⟶ Y⟦n⟧) ≃ₗ[R] Cocycle X Y n :=
  Cocycle.equivHomShift.toLinearEquiv (by simp)

def internalHomCohomologyType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (n : ℤ),
      (internalHomValue X Y).homology n ≃ₗ[R]
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj X ⟶
        (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj (Y⟦n⟧))

noncomputable def internalHomCohomologyValue (X Y : compValue.{v} R) (n : ℤ) :
    (internalHomValue X Y).homology n ≃ₗ[R]
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj X ⟶
        (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj (Y⟦n⟧)) :=
  (homologyLinearEquiv R X Y n).trans <|
    (CohomologyClass.homAddEquiv (K := X) (L := Y) (n := n)).toLinearEquiv (by
      intro r z
      obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
      simp [← CohomologyClass.mk_smul, CohomologyClass.toHom_mk])

def tensor_d_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] {P Q : compValue.{u} R} (i j t t' : ℤ) (ht : i + j = t)
     (ht' : t + 1 = t') (x : P.X i) (y : Q.X j),
      (HomologicalComplex.tensorObj P Q).d t t' (ιTensorObj P Q i j t ht (x ⊗ₜ[R] y)) =
      ιTensorObj P Q (i + 1) j t' (by omega) (P.d i (i + 1) x ⊗ₜ[R] y) +
      i.negOnePow • ιTensorObj P Q i (j + 1) t' (by omega) (x ⊗ₜ[R] Q.d j (j + 1) y)

def tensorMap_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] {P Q P' Q' : compValue.{u} R} (a : P' ⟶ P) (b : Q' ⟶ Q)
    (i j : ℤ) (x : P'.X i) (y : Q'.X j),
      (HomologicalComplex.tensorHom a b).f (i + j)
      (ιTensorObj P' Q' i j (i + j) rfl (x ⊗ₜ[R] y)) =
      ιTensorObj P Q i j (i + j) rfl (a.f i x ⊗ₜ[R] b.f j y)

def internalHomMap_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] {A A' B B' : compValue.{v} R} (g : A' ⟶ A) (h : B ⟶ B') {n i v : ℤ}
     (hi : i + n = v) (f : Cochain A B n) (x : A'.X i),
      ((internalHomMapValue g h).f n f).v i v hi x = h.f v (f.v i v hi (g.f i x))

def internalHom_d_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] {X Y : compValue.{v} R} (n i : ℤ) (f : Cochain X Y n) (x : X.X i),
      (((internalHomValue X Y).d n (n + 1) f).v i (i + n + 1) (by omega)) x =
      Y.d (i + n) (i + n + 1) (f.v i (i + n) rfl x) -
      n.negOnePow • f.v (i + 1) (i + n + 1) (by omega) (X.d i (i + 1) x)

def tensor_d_squaredType : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{u} R) (i j k : ℤ),
      (tensorComplexValue X Y).d i j ≫ (tensorComplexValue X Y).d j k = 0

def internalHom_d_squaredType : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R) (i j k : ℤ),
      (internalHomValue X Y).d i j ≫ (internalHomValue X Y).d j k = 0

def internalHom_boundary_zero_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] {X Y : compValue.{v} R} (f : X ⟶ Y),
      (∃ h : Cochain X Y (-1), δ (-1) 0 h = Cochain.ofHom f) ↔ Nonempty (Homotopy f 0)

def internalHom_boundary_shift_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] {X Y : compValue.{v} R} (n : ℤ) (z : Cocycle X Y n),
      (∃ h : Cochain X Y (n - 1), δ (n - 1) n h = z.1) ↔
      Nonempty (Homotopy ((internalHomCyclesShiftValue X Y n).symm z) 0)

def isKProjective_iff_internalHom_acyclicType : Prop :=
  ∀ {R : Type u} [CommRing R] (P : compValue.{v} R),
      isKProjectiveValue P ↔ ∀ A : compValue.{v} R, A.Acyclic → (internalHomValue P A).Acyclic

def isKInjective_iff_internalHom_acyclicType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : compValue.{v} R),
      isKInjectiveValue I ↔ ∀ A : compValue.{v} R, A.Acyclic → (internalHomValue A I).Acyclic

def tensorCofan_isColimitType : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{u} R) (n : ℤ),
    Nonempty (IsColimit (tensorCofanValue X Y n))

def internalHomMap_idType : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{v} R),
    internalHomMapValue (𝟙 X) (𝟙 Y) = 𝟙 (internalHomValue X Y)

def internalHomMap_compType : Prop :=
  ∀ {R : Type u} [CommRing R] {X X' X'' Y Y' Y'' : compValue.{v} R} (f : X' ⟶ X) (f' : X'' ⟶ X')
     (g : Y ⟶ Y') (g' : Y' ⟶ Y''),
      internalHomMapValue f g ≫ internalHomMapValue f' g' = internalHomMapValue (f' ≫ f) (g ≫ g')

def tensorMap_homotopyType : Prop :=
  ∀ {R : Type u} [CommRing R] {X X' Y Y' : compValue.{u} R} {f f' : X ⟶ X'} {g g' : Y ⟶ Y'}
     (h : Homotopy f f') (k : Homotopy g g'),
      Nonempty (Homotopy (tensorMapValue f g) (tensorMapValue f' g'))

def internalHomMap_homotopyType : Prop :=
  ∀ {R : Type u} [CommRing R] {X X' Y Y' : compValue.{v} R} {f f' : X' ⟶ X} {g g' : Y ⟶ Y'}
     (h : Homotopy f f') (k : Homotopy g g'),
      Nonempty (Homotopy (internalHomMapValue f g) (internalHomMapValue f' g'))

def tensorHomCurryingType : Prop :=
  ∀ (R : Type u) [CommRing R],
      ∃ e : ∀ P Q J : compValue.{u} R,
        internalHomValue (tensorComplexValue P Q) J ≅ internalHomValue P (internalHomValue Q J),
      (∀ (P Q J : compValue.{u} R) {n i j l m : ℤ}
          (hi : i + n = l) (hj : j + l = m)
          (f : Cochain (tensorComplexValue P Q) J n) (x : P.X i) (y : Q.X j),
        (((e P Q J).hom.f n f).v i l hi x).v j m hj y =
          f.v (i + j) m (by omega) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y))) ∧
      ∀ {P P' Q Q' J J' : compValue.{u} R} (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J'),
        internalHomMapValue (tensorMapValue a b) c ≫ (e P' Q' J').hom =
          (e P Q J).hom ≫ internalHomMapValue a (internalHomMapValue b c)

def tensorMap_idType : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{u} R),
    tensorMapValue (𝟙 X) (𝟙 Y) = 𝟙 (tensorComplexValue X Y)

def tensorMap_compType : Prop :=
  ∀ {R : Type u} [CommRing R] {X X' X'' Y Y' Y'' : compValue.{u} R} (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y''),
    tensorMapValue f g ≫ tensorMapValue f' g' = tensorMapValue (f ≫ f') (g ≫ g')

def tensorHomAdjunctionType : Prop :=
  ∀ (R : Type u) [CommRing R],
      ∃ e : ∀ P Q J : compValue.{u} R,
          (tensorComplexValue P Q ⟶ J) ≃ₗ[R] (P ⟶ internalHomValue Q J),
      (∀ (P Q J : compValue.{u} R) (f : tensorComplexValue P Q ⟶ J) (i j : ℤ)
          (x : P.X i) (y : Q.X j),
        ((e P Q J f).f i x).v j (i + j) (add_comm j i) y =
          f.f (i + j) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y))) ∧
      (∀ {P P' Q Q' J J' : compValue.{u} R} (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J')
          (f : tensorComplexValue P Q ⟶ J), e P' Q' J' (tensorMapValue a b ≫ f ≫ c) =
          a ≫ e P Q J f ≫ internalHomMapValue b c) ∧
      ∀ {P Q J : compValue.{u} R} (f f' : tensorComplexValue P Q ⟶ J),
        Nonempty (Homotopy f f') ↔ Nonempty (Homotopy (e P Q J f) (e P Q J f'))

end Specs.DerivedFormalization.CochainModels
