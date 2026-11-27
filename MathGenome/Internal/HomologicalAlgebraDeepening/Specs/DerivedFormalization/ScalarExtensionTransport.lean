import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ScalarExtensionModels
import Mathlib.CategoryTheory.Adjunction.Unique

/-! Ordinary scalar extension at a common coefficient bound. -/

namespace Specs.DerivedFormalization.ScalarExtensionTransport

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open Cochains (compValue)
open CochainModels (internalHomValue internalHomMapValue isKProjectiveValue tensorComplexValue)
open CochainTensor (tensor pure map isKFlat)
open CochainTensorTransport (AdequateModel representedUnit representedUnitZero)
open CochainRingTransport
  (representedExtension representedExtensionAdjunction complexFunctorValue conjugateValue
    complexRestrictionIsoValue adjunctionCompatible restrictionComp conjugateComp)
open CochainTensorMonoidal (tensorUnitValue tensorUnitZeroValue pureTensorValue)
open DerivedRestriction (restrictScalarsComplexValue)
open ScalarExtensionModels (extendScalarsComplexValue)
open CochainComplex.HomComplex (Cochain)

universe u w z a


noncomputable section

section Adjunction

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F : C ⥤ D} {G : D ⥤ C} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- The adjunction whose unit and counit act degreewise. -/
def cochainAdjunction (adj : F ⊣ G) :
    F.mapHomologicalComplex (.up ℤ) ⊣ G.mapHomologicalComplex (.up ℤ) where
  unit := adj.unit.mapHomologicalComplex (.up ℤ)
  counit := adj.counit.mapHomologicalComplex (.up ℤ)
  left_triangle_components X := by
    apply HomologicalComplex.hom_ext
    intro i
    exact adj.left_triangle_components (X.X i)
  right_triangle_components Y := by
    apply HomologicalComplex.hom_ext
    intro i
    exact adj.right_triangle_components (Y.X i)

end Adjunction

variable {R : Type u} {S : Type w} {T : Type z} {A B C : Type a}
  [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
  (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)

/-- Degreewise extension with target ring represented at the common bound. -/
abbrev extension : compValue.{a} R ⥤ compValue.{a} S :=
  (representedExtension d f).mapHomologicalComplex (.up ℤ)

abbrev extensionAdjunction : extension d f ⊣ restrictScalarsComplexValue.{a} f :=
  cochainAdjunction (representedExtensionAdjunction d f)

/-- The homogeneous element of extension determined by an original scalar and element. -/
abbrev extendPure (X : compValue.{a} R) (i : ℤ) (s : S) (x : X.X i) :
    ((extension d f).obj X).X i :=
  d s ⊗ₜ[R,d.toRingHom.comp f] x

/-- Restriction is the actual degreewise functor at the representative's bound. -/
abbrev restriction (_d : S ≃+* B) (f : R →+* S) : compValue.{a} S ⥤ compValue.{a} R :=
  restrictScalarsComplexValue f

local notation "L" => extension d f
local notation "U" => restriction d f

/-- The balanced cancellation map and signed Hom adjunction use the original
complexes and all acyclic tests at their common coefficient bound. -/
structure ModelStability where
  cancel (E : compValue.{a} S) (P : compValue.{a} R) :
    (U).obj (tensor E ((L).obj P)) ≅ tensor ((U).obj E) P
  cancel_on_pure (E : compValue.{a} S) (P : compValue.{a} R)
      {i j n : ℤ} (h : i + j = n) (x : E.X i) (s : S) (y : P.X j) :
    (cancel E P).hom.f n (pure E ((L).obj P) h x (extendPure d f P j s y)) =
      pure ((U).obj E) P h (show ((U).obj E).X i from s • x) y
  cancel_natural {E E' : compValue.{a} S} {P P' : compValue.{a} R}
      (b : E ⟶ E') (p : P ⟶ P') :
    (U).map (map b ((L).map p)) ≫ (cancel E' P').hom =
      (cancel E P).hom ≫ map ((U).map b) p
  homIso (P : compValue.{a} R) (E : compValue.{a} S) :
    (U).obj (internalHomValue ((L).obj P) E) ≅ internalHomValue P ((U).obj E)
  hom_on_eval (P : compValue.{a} R) (E : compValue.{a} S)
      {q i j : ℤ} (h : i + q = j) (k : Cochain ((L).obj P) E q) (x : P.X i) :
    ((homIso P E).hom.f q k).v i j h x = k.v i j h (extendPure d f P i 1 x)
  hom_inverse_on_eval (P : compValue.{a} R) (E : compValue.{a} S)
      {q i j : ℤ} (h : i + q = j) (k : Cochain P ((U).obj E) q) (x : P.X i) (s : S) :
    ((homIso P E).inv.f q k).v i j h (extendPure d f P i s x) =
      s • (show E.X j from k.v i j h x)
  hom_natural {P P' : compValue.{a} R} {E E' : compValue.{a} S}
      (p : P' ⟶ P) (b : E ⟶ E') :
    (U).map (internalHomMapValue ((L).map p) b) ≫ (homIso P' E').hom =
      (homIso P E).hom ≫ internalHomMapValue p ((U).map b)
  acyclic_iff (E : compValue.{a} S) : ((U).obj E).Acyclic ↔ E.Acyclic
  preserves_kFlat (P : compValue.{a} R) : isKFlat P → isKFlat ((L).obj P)
  preserves_kProjective (P : compValue.{a} R) :
    isKProjectiveValue P → isKProjectiveValue ((L).obj P)

def modelStabilityType : Prop :=
  ∀ {R : Type u} {S : Type w} {B : Type a} [CommRing R] [CommRing S] [CommRing B]
    (d : S ≃+* B) (f : R →+* S), Nonempty (ModelStability d f)

section Monoidal

variable (MR : AdequateModel e) (MS : AdequateModel d)

attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

abbrev diagonalExtension : compValue.{a} A ⥤ compValue.{a} B :=
  extendScalarsComplexValue (conjugateValue e d f)

abbrev diagonalAdjunction :
    diagonalExtension e d f ⊣ restrictScalarsComplexValue.{a} (conjugateValue e d f) :=
  cochainAdjunction (ModuleCat.extendRestrictScalarsAdj.{a} (conjugateValue e d f))

local notation "FN" => diagonalExtension e d f
local notation "FS" => complexFunctorValue d
local notation "FR" => complexFunctorValue e

/-- Ordinary symmetric monoidal extension and the lax structure on the actual
restriction, with their comparisons on signed homogeneous generators. -/
structure MonoidalChange where
  extensionBraided :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    (L).Braided
  restrictionLax :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    (U).LaxMonoidal
  mates :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := extensionBraided
    letI := restrictionLax
    (extensionAdjunction d f).IsMonoidal
  tensor_on_pure (X Y : compValue.{a} R) {i j n : ℤ} (h : i + j = n)
      (s t : S) (x : X.X i) (y : Y.X j) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := extensionBraided
    let b := MS.tensorModel ((L).obj X) ((L).obj Y) ≪≫ Functor.Monoidal.μIso L X Y ≪≫
      (L).mapIso (MR.tensorModel X Y).symm
    b.hom.f n (pure ((L).obj X) ((L).obj Y) h (extendPure d f X i s x) (extendPure d f Y j t y)) =
      extendPure d f (tensor X Y) n (s * t) (pure X Y h x y)
  unit_on_pure (b : B) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := extensionBraided
    let j := MS.unitModel ≪≫ Functor.Monoidal.εIso L ≪≫ (L).mapIso MR.unitModel.symm
    j.hom.f 0 ((representedUnitZero d).inv b) =
      extendPure d f (representedUnit e) 0 (d.symm b) ((representedUnitZero e).inv (1 : A))
  restrict_tensor_on_pure (X Y : compValue.{a} S) {i j n : ℤ} (h : i + j = n)
      (x : X.X i) (y : Y.X j) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := restrictionLax
    let b := (MR.tensorModel ((U).obj X) ((U).obj Y)).hom ≫
      Functor.LaxMonoidal.μ U X Y ≫ (U).map (MS.tensorModel X Y).inv
    b.f n (pure ((U).obj X) ((U).obj Y) h x y) = pure X Y h x y
  restrict_unit_on_pure (r : A) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := restrictionLax
    let b := MR.unitModel.hom ≫ Functor.LaxMonoidal.ε U ≫ (U).map MS.unitModel.inv
    b.f 0 ((representedUnitZero e).inv r) =
      (representedUnitZero d).inv ((conjugateValue e d f) r)

/-- The diagonal model uses degreewise Mathlib extension on the represented
rings and the native signed diagonal tensors. -/
structure DiagonalComparison (M : MonoidalChange e d f MR MS) where
  nativeBraided :
    letI := MR.nativeSymmetric
    letI := MS.nativeSymmetric
    (FN).Braided
  comparison : L ⋙ FS ≅ FR ⋙ FN
  comparison_adjunction :
    adjunctionCompatible (extensionAdjunction d f)
      (diagonalAdjunction e d f)
      comparison.inv (complexRestrictionIsoValue e d f).hom
  comparison_on_pure (X : compValue.{a} R) (i : ℤ) (s : S) (x : X.X i) :
    (comparison.hom.app X).f i (extendPure d f X i s x) =
      (show ((FN).obj ((FR).obj X)).X i from d s ⊗ₜ[A,conjugateValue e d f] (show ((FR).obj X).X i from x))
  native_tensor_on_pure (X Y : compValue.{a} A) {i j n : ℤ} (h : i + j = n)
      (s t : B) (x : X.X i) (y : Y.X j) :
    letI := MR.nativeSymmetric
    letI := MS.nativeSymmetric
    letI := nativeBraided
    (Functor.LaxMonoidal.μ FN X Y).f n
      (pureTensorValue ((FN).obj X) ((FN).obj Y) i j h
        (s ⊗ₜ[A,conjugateValue e d f] x) (t ⊗ₜ[A,conjugateValue e d f] y)) =
      (show ((FN).obj (tensorComplexValue X Y)).X n from
        (s * t) ⊗ₜ[A,conjugateValue e d f] pureTensorValue X Y i j h x y)
  native_unit_on_pure (b : B) :
    letI := MR.nativeSymmetric
    letI := MS.nativeSymmetric
    letI := nativeBraided
    (Functor.LaxMonoidal.ε FN).f 0 ((tensorUnitZeroValue B).inv b) =
      (show ((FN).obj (tensorUnitValue A)).X 0 from
        b ⊗ₜ[A,conjugateValue e d f] (tensorUnitZeroValue A).inv (1 : A))
  monoidal :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := MR.nativeSymmetric
    letI := MS.nativeSymmetric
    letI := MR.chainTransport
    letI := MS.chainTransport
    letI := M.extensionBraided
    letI := nativeBraided
    NatTrans.IsMonoidal comparison.hom

end Monoidal

def monoidalComparisonType : Prop :=
  ∀ {R : Type u} {S : Type w} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    ∀ (MR : AdequateModel e) (MS : AdequateModel d),
      ∃ M : MonoidalChange e d f MR MS, Nonempty (DiagonalComparison e d f MR MS M)

section NativeExtension

variable {B' : Type (max w a)} [CommRing B'] (d' : S ≃+* B')

/-- Canonical comparison with the existing degreewise extension when the
extending ring itself fits in the coefficient universe. -/
def nativeExtensionIso :
    extendScalarsComplexValue.{u,w,a} f ≅ extension d' f :=
  (cochainAdjunction (ModuleCat.extendRestrictScalarsAdj.{a} f)).leftAdjointUniq
    (extensionAdjunction d' f)

def nativeExtensionType : Prop :=
  ∀ {R : Type u} {S : Type w} {B : Type (max w a)} [CommRing R] [CommRing S] [CommRing B]
    (d : S ≃+* B) (f : R →+* S)
    (X : compValue.{max w a} R) (i : ℤ) (s : S) (x : X.X i),
    ((nativeExtensionIso f d).hom.app X).f i (s ⊗ₜ[R,f] x) = extendPure d f X i s x

end NativeExtension

section Composition

variable (c : T ≃+* C) (g : S →+* T)

local notation "Lg" => extension c g
local notation "Lgf" => extension c (g.comp f)

/-- Transitivity is the adjunction mate of composition for the actual
restriction functors. -/
def compositionIso : L ⋙ Lg ≅ Lgf :=
  (((extensionAdjunction d f).comp (extensionAdjunction c g)).ofNatIsoRight
    ((Functor.mapHomologicalComplexCompIso (Iso.refl
      (ModuleCat.restrictScalars.{a} g ⋙ ModuleCat.restrictScalars.{a} f)) (.up ℤ)) ≪≫
      NatIso.mapHomologicalComplex (restrictionComp.{a} f g) (.up ℤ))).leftAdjointUniq
    (extensionAdjunction c (g.comp f))

/-- The same adjunction mate on the diagonal representatives. -/
def diagonalCompositionIso :
    diagonalExtension e d f ⋙ diagonalExtension d c g ≅ diagonalExtension e c (g.comp f) :=
  (((diagonalAdjunction e d f).comp (diagonalAdjunction d c g)).ofNatIsoRight
    ((Functor.mapHomologicalComplexCompIso (Iso.refl
      (ModuleCat.restrictScalars.{a} (conjugateValue d c g) ⋙
        ModuleCat.restrictScalars.{a} (conjugateValue e d f))) (.up ℤ)) ≪≫
      NatIso.mapHomologicalComplex (conjugateComp e d c f g) (.up ℤ))).leftAdjointUniq
    (diagonalAdjunction e c (g.comp f))

/-- Transitivity acts by multiplication of the two extending scalars
and is monoidal for the generator-preserving structures. -/
def compositionType : Prop :=
  ∀ {R : Type u} {S : Type w} {T : Type z} {A B C : Type a}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
    (e : R ≃+* A) (d : S ≃+* B) (c : T ≃+* C) (f : R →+* S) (g : S →+* T),
    (∀ (X : compValue.{a} R) (i : ℤ) (s : S) (t : T) (x : X.X i),
      ((compositionIso d f c g).hom.app X).f i
        (extendPure c g ((extension d f).obj X) i t (extendPure d f X i s x)) =
      extendPure c (g.comp f) X i (t * g s) x) ∧
    (∀ (MR : AdequateModel e) (MS : AdequateModel d) (MT : AdequateModel c)
      (F : MonoidalChange e d f MR MS) (G : MonoidalChange d c g MS MT)
      (GF : MonoidalChange e c (g.comp f) MR MT),
      letI := MR.chainMonoidal
      letI := MS.chainMonoidal
      letI := MT.chainMonoidal
      letI := MR.chainSymmetric
      letI := MS.chainSymmetric
      letI := MT.chainSymmetric
      letI := F.extensionBraided
      letI := G.extensionBraided
      letI := GF.extensionBraided
      NatTrans.IsMonoidal (compositionIso d f c g).hom) ∧
    ∀ {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}
      {F : MonoidalChange e d f MR MS} {G : MonoidalChange d c g MS MT}
      {GF : MonoidalChange e c (g.comp f) MR MT}
      (DF : DiagonalComparison e d f MR MS F) (DG : DiagonalComparison d c g MS MT G)
      (DGF : DiagonalComparison e c (g.comp f) MR MT GF) (X : compValue.{a} R),
      (complexFunctorValue c).map ((compositionIso d f c g).hom.app X) ≫
        DGF.comparison.hom.app X =
      DG.comparison.hom.app ((extension d f).obj X) ≫
        (diagonalExtension d c g).map (DF.comparison.hom.app X) ≫
        (diagonalCompositionIso e d f c g).hom.app ((complexFunctorValue e).obj X)

end Composition

end

end Specs.DerivedFormalization.ScalarExtensionTransport
