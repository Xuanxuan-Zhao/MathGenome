import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentModelProperties
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoefficientLift

open CategoryTheory

universe u v t

namespace Specs.DerivedFormalization.Affine.CotangentComplex

open _root_.DerivedFormalization
open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Kahler (DifferentialModel value)
open Tensor (ModuleTensor dgCat regular term)
open CotangentModelProperties (cotangentModel)
open DG.HomComplex (gradedHom component homotopyCategory homotopyClass HomotopyEquation)
open DG.KProjective (isKProjective)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}

abbrev oneObject (B : NonpositiveCDGA.{u,v} k) := dgCat B.toCommDGAlgebra

/-- A semifree surjective resolution of a specified algebra map, with its
actual factorization and augmentation. -/
structure Resolution (b : A ⟶ B) where
  algebra : NonpositiveCDGA.{u,v} k
  base : A ⟶ algebra
  augmentation : algebra ⟶ B
  triangle : base ≫ augmentation = b
  semifree : Semifree.IsSemifree A base
  surjective : NonpositiveCDGA.DegreewiseSurjective augmentation
  quasiIso : NonpositiveCDGA.IsQuasiIso augmentation

/-- A resolution equipped with its module of relative differentials. -/
structure Model (b : A ⟶ B) extends Resolution b where
  differentials : DifferentialModel
    (base : A.toCommDGAlgebra ⟶ algebra.toCommDGAlgebra)

/-- The strict representative (B ⊗_P Ω_{P/A}). -/
abbrev Model.module (R : Model b) (T : ModuleTensor.{u,v} k) : B.Module :=
  cotangentModel T R.augmentation R.differentials

/-- A comparison of resolutions is a strict algebra map over the base and
the augmentation. -/
structure Lift (R S : Model b) where
  hom : R.algebra ⟶ S.algebra
  base_comm : R.base ≫ hom = S.base
  augmentation_comm : hom ≫ S.augmentation = R.augmentation

def Lift.id (R : Model b) : Lift R R := ⟨𝟙 _, Category.comp_id _, Category.id_comp _⟩

def Lift.comp {R S U : Model b} (f : Lift R S) (g : Lift S U) : Lift R U where
  hom := f.hom ≫ g.hom
  base_comm := by rw [← Category.assoc, f.base_comm, g.base_comm]
  augmentation_comm := by rw [Category.assoc, g.augmentation_comm, f.augmentation_comm]

/-- A map induced by a lift takes every extended differential symbol to
the differential of its image, with the same scalar in (B). -/
def Induced (T : ModuleTensor.{u,v} k) {R S : Model b} (f : Lift R S)
    (c : R.module T ⟶ S.module T) : Prop :=
  ∀ (i j n : ℤ) (e : i + j = n) (x : R.algebra.complex.X i) (a : B.complex.X j),
    (c.app ()).f n
        (T.tmul R.augmentation (N := regular B.toCommDGAlgebra) i j n e
          (value R.differentials.symbol i i (add_zero i) x) a) =
      T.tmul S.augmentation (N := regular B.toCommDGAlgebra) i j n e
        (value S.differentials.symbol i i (add_zero i) (f.hom.chainMap.f i x)) a

/-- The class of a strict comparison in the actual one-object module
homotopy category. -/
abbrev moduleClass (h : DG.Derived.HomotopyCategoryLaws (oneObject B))
    {M N : B.Module} (c : M ⟶ N) :
    @Quiver.Hom (homotopyCategory (oneObject B))
      (DG.Derived.homotopyCategory (oneObject B) h).toQuiver M N :=
  homotopyClass c

abbrev comparisonClass (h : DG.Derived.HomotopyCategoryLaws (oneObject B))
    {R S : Model b} {T : ModuleTensor.{u,v} k} (c : R.module T ⟶ S.module T) :=
  moduleClass h c

abbrev localizedModel (h : DG.Derived.HomotopyCategoryLaws (oneObject B))
    (R : Model b) (T : ModuleTensor.{u,v} k) : DG.Derived.derivedCategory (oneObject B) h :=
  letI := DG.Derived.homotopyCategory (oneObject B) h
  letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject B) h
  (DG.Derived.quotient (oneObject B) h).obj (R.module T)

def localizedComparison (h : DG.Derived.HomotopyCategoryLaws (oneObject B))
    {R S : Model b} {T : ModuleTensor.{u,v} k} (c : R.module T ⟶ S.module T) :
    letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject B) h
    localizedModel h R T ⟶ localizedModel h S T :=
  letI := DG.Derived.homotopyCategory (oneObject B) h
  letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject B) h
  (DG.Derived.quotient (oneObject B) h).map (comparisonClass h c)

/-- The comparison system for all resolutions of one algebra map. Its
selected resolution represents the cotangent complex. -/
structure ComparisonSystem (T : ModuleTensor.{u,v} k) (b : A ⟶ B)
    (h : DG.Derived.HomotopyCategoryLaws (oneObject B)) where
  chosen : Model b
  lift (R S : Model b) : Lift R S
  map {R S : Model b} (f : Lift R S) : R.module T ⟶ S.module T
  induced {R S : Model b} (f : Lift R S) : Induced T f (map f)
  unique {R S : Model b} (f : Lift R S) (c : R.module T ⟶ S.module T) :
    Induced T f c → c = map f
  homotopy {R S : Model b} (f g : Lift R S) :
    ∃ s : gradedHom (R.module T) (S.module T) (-1), HomotopyEquation (map f) (map g) s
  properties (R : Model b) : isKProjective (R.module T) ∧ T.KFlat (R.module T)
  identity (R : Model b) :
    letI := DG.Derived.homotopyCategory (oneObject B) h
    comparisonClass h (map (lift R R)) =
      @CategoryStruct.id (homotopyCategory (oneObject B))
        (DG.Derived.homotopyCategory (oneObject B) h).toCategoryStruct (R.module T)
  cocycle (R S U : Model b) :
    letI := DG.Derived.homotopyCategory (oneObject B) h
    comparisonClass h (map (lift R S)) ≫ comparisonClass h (map (lift S U)) =
      comparisonClass h (map (lift R U))
  iso {R S : Model b} (f : Lift R S) :
    letI := DG.Derived.homotopyCategory (oneObject B) h
    IsIso (comparisonClass h (map f))
  independence {R S : Model b} (f g : Lift R S) :
    comparisonClass h (map f) = comparisonClass h (map g)

/-- The cotangent complex represented by the selected resolution in the
homotopy category of dg modules over the original algebra. -/
abbrev ComparisonSystem.homotopyObject {T : ModuleTensor.{u,v} k}
    {h : DG.Derived.HomotopyCategoryLaws (oneObject B)} (C : ComparisonSystem T b h) :
    homotopyCategory (oneObject B) :=
  C.chosen.module T

/-- The same representative in the native derived category. -/
abbrev ComparisonSystem.derivedObject {T : ModuleTensor.{u,v} k}
    {h : DG.Derived.HomotopyCategoryLaws (oneObject B)} (C : ComparisonSystem T b h) :=
  localizedModel h C.chosen T

/-- The canonical comparison is already an isomorphism before localization. -/
def ComparisonSystem.homotopyIso {T : ModuleTensor.{u,v} k}
    {h : DG.Derived.HomotopyCategoryLaws (oneObject B)} (C : ComparisonSystem T b h)
    (R S : Model b) :
    @Iso (homotopyCategory (oneObject B))
      (DG.Derived.homotopyCategory (oneObject B) h) (R.module T) (S.module T) := by
  letI := DG.Derived.homotopyCategory (oneObject B) h
  letI := C.iso (C.lift R S)
  exact asIso (comparisonClass h (C.map (C.lift R S)))

/-- Derived comparison on the same represented objects and maps. -/
def ComparisonSystem.derivedIso {T : ModuleTensor.{u,v} k}
    {h : DG.Derived.HomotopyCategoryLaws (oneObject B)} (C : ComparisonSystem T b h)
    (R S : Model b) :
    letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject B) h
    localizedModel h R T ≅ localizedModel h S T :=
  letI := DG.Derived.homotopyCategory (oneObject B) h
  letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject B) h
  (DG.Derived.quotient (oneObject B) h).mapIso (C.homotopyIso R S)

def NativeComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    (b : A ⟶ B) (T : ModuleTensor.{u,v} k)
    (h : DG.Derived.HomotopyCategoryLaws (oneObject B)),
    (∀ {P Q : CommDGAlgebra.{u,v} k} (f : P ⟶ Q) (N : Q.Module), T.Formulas f N) →
    Nonempty (ComparisonSystem T b h)

/-- Every map of nonpositive cdgas has a cotangent complex with these
representatives and canonical comparisons. -/
def CotangentExists : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k} (b : A ⟶ B),
    ∃ (T : ModuleTensor.{u,v} k) (h : DG.Derived.HomotopyCategoryLaws (oneObject B)),
      (∀ {P Q : CommDGAlgebra.{u,v} k} (f : P ⟶ Q) (N : Q.Module), T.Formulas f N) ∧
      Nonempty (ComparisonSystem T b h)

section Coefficients

open DG.CoefficientLift (liftCategory liftMap)
open DG.CoefficientLiftComparison (complexLift)

set_option linter.checkUnivs false

/-- Coefficient enlargement of the same cdga by conjugating its operations
with the degreewise (k)-linear lifts. -/
@[reducible] def liftCDGA (P : NonpositiveCDGA.{u,v} k) : NonpositiveCDGA.{u,max v t} k where
  toCommDGAlgebra :=
    { toDGAlgebra := (liftCategory.{u,v,0,t} (oneObject P)).toData
      graded_comm := fun i j n h x y =>
        ULift.ext (P.toCommDGAlgebra.graded_comm i j n h x.down y.down) }
  nonpositive i hi :=
    ⟨fun x y => ULift.ext ((P.nonpositive i hi).elim x.down y.down)⟩

@[reducible] def cdgaLift (k : Type u) [Field k] [CharZero k] :
    NonpositiveCDGA.{u,v} k ⥤ NonpositiveCDGA.{u,max v t} k where
  obj := liftCDGA.{u,v,t}
  map f :=
    { chainMap := (complexLift.{u,v,t} k).map f.chainMap
      map_one := ULift.ext f.map_one
      map_mul := fun i j n h x y => ULift.ext (f.map_mul i j n h x.down y.down) }
  map_id P := CommDGAlgebra.Hom.ext_chainMap ((complexLift.{u,v,t} k).map_id P.complex)
  map_comp f g := CommDGAlgebra.Hom.ext_chainMap
    ((complexLift.{u,v,t} k).map_comp f.chainMap g.chainMap)

/-- The transported presentation has the original generators in the
original degrees and the original order of stages. -/
abbrev liftVariables (V : Semifree.Variables.{v}) : Semifree.Variables.{max v t} where
  Index := ULift.{t} V.Index
  degree x := V.degree x.down
  nonpositive x := V.nonpositive x.down

def PresentationEnlargement : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A P : NonpositiveCDGA.{u,v} k}
    (f : A ⟶ P) (V : Semifree.Variables.{v}) (E : Semifree.StagedPresentation A V f),
    let F := cdgaLift.{u,v,t} k
    let W := liftVariables.{v,t} V
    ∃ E' : Semifree.StagedPresentation (F.obj A) W (F.map f),
      (∀ x : V.Index, E'.component (V.degree x) (Semifree.variableTerm (F.obj A) W (ULift.up x)) =
        ULift.up (E.component (V.degree x) (Semifree.variableTerm A V x))) ∧
      ∃ e : E'.stages.Stage ≃ E.stages.Stage,
        (∀ x : V.Index, e (E'.stages.stage (ULift.up x)) = E.stages.stage x) ∧
        ∀ a c : E'.stages.Stage, a < c ↔ e a < e c

open DG.AmbientDerived (strictInput)

variable {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}

/-- A model at the new coefficient bound with the lifted resolution and
the identified differential symbols and pure tensors. -/
structure LiftedModel (T : ModuleTensor.{u,v} k) (T' : ModuleTensor.{u,max v t} k)
    (R : Model b) where
  semifree : Semifree.IsSemifree (liftCDGA.{u,v,t} A) ((cdgaLift.{u,v,t} k).map R.base)
  surjective : NonpositiveCDGA.DegreewiseSurjective ((cdgaLift.{u,v,t} k).map R.augmentation)
  quasiIso : NonpositiveCDGA.IsQuasiIso ((cdgaLift.{u,v,t} k).map R.augmentation)
  differentials : DifferentialModel
    (show (liftCDGA.{u,v,t} A).toCommDGAlgebra ⟶ (liftCDGA.{u,v,t} R.algebra).toCommDGAlgebra
      from (cdgaLift.{u,v,t} k).map R.base)
  differentialIso : (strictInput.{u,v,0,t} (oneObject R.algebra)).obj R.differentials.module ≅
    differentials.module
  symbol (i : ℤ) (x : R.algebra.complex.X i) :
    (differentialIso.hom.app ()).f i
        (ULift.up (value R.differentials.symbol i i (add_zero i) x)) =
      value differentials.symbol i i (add_zero i) (ULift.up x)
  cotangentIso : (strictInput.{u,v,0,t} (oneObject B)).obj (R.module T) ≅
    cotangentModel T' ((cdgaLift.{u,v,t} k).map R.augmentation) differentials
  tensor (i j n : ℤ) (e : i + j = n) (x : term R.differentials.module i) (a : B.complex.X j) :
    (cotangentIso.hom.app ()).f n
      (ULift.up (T.tmul R.augmentation (N := regular B.toCommDGAlgebra) i j n e x a)) =
    T'.tmul ((cdgaLift.{u,v,t} k).map R.augmentation)
      (N := regular (liftCDGA.{u,v,t} B).toCommDGAlgebra)
      i j n e ((differentialIso.hom.app ()).f i (ULift.up x)) (ULift.up a)

/-- The enlarged object uses literally the original base map and
augmentation after applying the coefficient functor. -/
abbrev LiftedModel.model {R : Model b} (U : LiftedModel T T' R) :
    Model ((cdgaLift.{u,v,t} k).map b) where
  algebra := liftCDGA.{u,v,t} R.algebra
  base := (cdgaLift.{u,v,t} k).map R.base
  augmentation := (cdgaLift.{u,v,t} k).map R.augmentation
  triangle := by rw [← Functor.map_comp, R.triangle]
  semifree := U.semifree
  surjective := U.surjective
  quasiIso := U.quasiIso
  differentials := U.differentials

def LiftedModel.lift {R S : Model b} (U : LiftedModel T T' R) (V : LiftedModel T T' S)
    (f : Lift R S) : Lift U.model V.model where
  hom := (cdgaLift.{u,v,t} k).map f.hom
  base_comm := by
    change (cdgaLift.{u,v,t} k).map R.base ≫ (cdgaLift.{u,v,t} k).map f.hom =
      (cdgaLift.{u,v,t} k).map S.base
    rw [← Functor.map_comp, f.base_comm]
  augmentation_comm := by
    change (cdgaLift.{u,v,t} k).map f.hom ≫ (cdgaLift.{u,v,t} k).map S.augmentation =
      (cdgaLift.{u,v,t} k).map R.augmentation
    rw [← Functor.map_comp, f.augmentation_comm]

/-- Coefficient transport of the strict comparison, expressed on the
cotangent models constructed at the enlarged level. -/
def LiftedModel.map {R S : Model b} (U : LiftedModel T T' R) (V : LiftedModel T T' S)
    (c : R.module T ⟶ S.module T) : U.model.module T' ⟶ V.model.module T' :=
  U.cotangentIso.inv ≫ liftMap.{u,v,0,t} c ≫ V.cotangentIso.hom

def ModelEnlargement : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}
    (R : Model b) (T : ModuleTensor.{u,v} k) (T' : ModuleTensor.{u,max v t} k),
    (∀ {P Q : CommDGAlgebra.{u,v} k} (p : P ⟶ Q) (N : Q.Module), T.Formulas p N) →
    (∀ {P Q : CommDGAlgebra.{u,max v t} k} (p : P ⟶ Q) (N : Q.Module), T'.Formulas p N) →
    Nonempty (LiftedModel T T' R)

/-- Comparison maps and specified homotopies are carried to those on the
enlarged cotangent models by coefficient conjugation. -/
def ComparisonEnlargement : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}
    {R S : Model b} {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    (U : LiftedModel T T' R) (V : LiftedModel T T' S),
    (∀ (f : Lift R S) (c : R.module T ⟶ S.module T),
      Induced T f c → Induced T' (U.lift V f) (U.map V c)) ∧
    ∀ (c d : R.module T ⟶ S.module T) (s : gradedHom (R.module T) (S.module T) (-1)),
      HomotopyEquation c d s →
      ∃ s' : gradedHom (U.model.module T') (V.model.module T') (-1),
        HomotopyEquation (U.map V c) (U.map V d) s' ∧
        ∀ (i j : ℤ) (e : i + (-1) = j) (x : term (U.model.module T') i),
          component s' () i j e x =
            (V.cotangentIso.hom.app ()).f j
              (ULift.up (component s () i j e (((U.cotangentIso.inv.app ()).f i x).down)))

/-- At a common adequate bound the localization square sends each
representative and comparison to the corresponding enlarged one. -/
def LocalizedEnlargement : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}
    {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    (h : DG.Derived.HomotopyCategoryLaws (oneObject B))
    (h' : DG.Derived.HomotopyCategoryLaws (oneObject (liftCDGA.{u,v,t} B))),
    letI := DG.Derived.homotopyCategory (oneObject B) h
    letI := DG.Derived.homotopyCategory (oneObject (liftCDGA.{u,v,t} B)) h'
    letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject B) h
    letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject (liftCDGA.{u,v,t} B)) h'
    ∃ D : DG.DerivedCoefficientLift.Descent h h' (strictInput.{u,v,0,t} (oneObject B)),
      D.FullyFaithful ∧
      ∀ U : ∀ R : Model b, LiftedModel T T' R,
        ∃ I : ∀ R : Model b, D.D.obj (localizedModel h R T) ≅ localizedModel h' (U R).model T',
          (∀ R, (I R).hom = (D.representedIso (R.module T)).hom ≫
              (DG.Derived.quotient _ h').map (moduleClass h' (U R).cotangentIso.hom)) ∧
          ∀ {R S : Model b} (c : R.module T ⟶ S.module T),
            D.D.map (localizedComparison h c) ≫ (I S).hom =
              (I R).hom ≫ localizedComparison h' ((U R).map (U S) c)

end Coefficients

end

end Specs.DerivedFormalization.Affine.CotangentComplex
