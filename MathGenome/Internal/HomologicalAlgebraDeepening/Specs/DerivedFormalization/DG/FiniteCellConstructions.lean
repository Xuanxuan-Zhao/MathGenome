import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CellReindex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLift

open CategoryTheory

universe u v w j t

namespace Specs.DerivedFormalization.DG.FiniteCellConstructions

open _root_.DerivedFormalization
open SemiFree (attach attachedGenerator CellFamily cell directSum finiteCell generator inclusion)
open ShiftCone (cone coneInclusion shift)
open Yoneda (representable)
open HomComplex (dgModuleCategory)

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

/-- The chosen index type for writing a sum of n modules. -/
abbrev FiniteIndex (n : ℕ) := ULift.{v} (Fin n)

/-- The written finite sum, including the empty sum. -/
abbrev finiteSum {n : ℕ} (F : Fin n → RightDGModuleModel A) : RightDGModuleModel A :=
  directSum (I := FiniteIndex.{v} n) fun i => F i.down

abbrev zeroModule (A : DGCategoryModel.{u,v,w} k) : RightDGModuleModel A :=
  finiteSum (n := 0) Fin.elim0

/-- The one-cell extension with prescribed differential of the generator. -/
def singletonCell (P : RightDGModuleModel A) (a : A.Obj) (n : ℤ)
    (z : (P.complex a).X (n+1)) (hz : (P.complex a).d (n+1) (n+1+1) z = 0) :
    CellFamily P (FiniteIndex.{v} 1) where
  object _ := a
  degree _ := n
  boundary _ := z
  closed _ := hz

def FiniteCellZero : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    finiteCell (zeroModule A)

def FiniteCellRepresentable : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (a : A.Obj),
    finiteCell (representable a)

def FiniteCellShift : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (s : ℤ), finiteCell M → finiteCell (shift M s)

def FiniteCellSum : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type v} [Finite I] (F : I → RightDGModuleModel A),
    (∀ i, finiteCell (F i)) → finiteCell (directSum F)

def FiniteCellCone : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q : RightDGModuleModel A} (f : P ⟶ Q),
    finiteCell P → finiteCell Q → finiteCell (cone f)

/-- The cone of the closed map out of the cell in degree n+1 is the
attachment in degree n. The component formula specifies the map on every
homogeneous multiple of the generator. -/
def SingletonAttachmentCone : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (P : RightDGModuleModel A) (a : A.Obj) (n : ℤ)
    (z : (P.complex a).X (n+1)) (hz : (P.complex a).d (n+1) (n+1+1) z = 0),
    let C := singletonCell P a n z hz
    ∃ f : cell a (n+1) ⟶ P,
      (∀ (b : A.Obj) (i : ℤ) (x : (A.hom b a).X (i + -(n+1))),
        (f.app b).f i x = P.act (n+1) (i + -(n+1)) i (by omega) z x) ∧
      ∃ e : attach C ≅ cone f,
        inclusion C ≫ e.hom = coneInclusion f ∧
        (e.hom.app a).f n (attachedGenerator C ⟨0⟩) = (0, generator a (n+1))

/-- Operations used to form the next set of written modules from the previous
one. Strict maps are the closed degree-zero maps of right dg modules. -/
inductive WrittenStep (A : DGCategoryModel.{u,v,w} k) {I : Type (max v w)}
    (eval : I → RightDGModuleModel A) : Type (max v w) where
  | previous (i : I)
  | shift (i : I) (s : ℤ)
  | sum (n : ℕ) (F : Fin n → I)
  | cone (i j : I) (f : eval i ⟶ eval j)

/-- A small type of codes and its evaluation for each finite stage.
The base stage consists of the representables and the empty sum. -/
def writtenStage (A : DGCategoryModel.{u,v,w} k) (j : ℕ) :
    Σ I : Type (max v w), I → RightDGModuleModel A :=
  Nat.rec
    ⟨ULift.{v} A.Obj ⊕ Unit, Sum.elim (fun a => representable a.down)
      (fun _ => zeroModule A)⟩
    (fun _ prev => ⟨WrittenStep A prev.2, fun
      | .previous i => prev.2 i
      | .shift i s => shift (prev.2 i) s
      | .sum _ F => finiteSum (prev.2 ∘ F)
      | .cone _ _ f => cone f⟩)
    j

abbrev WrittenCode (A : DGCategoryModel.{u,v,w} k) :=
  Σ j : ℕ, (writtenStage A j).1

def evalWrittenCode (A : DGCategoryModel.{u,v,w} k) (c : WrittenCode A) :
    RightDGModuleModel A :=
  (writtenStage A c.1).2 c.2

/-- The set of written objects is the union of the images of the finite stages. -/
def writtenSet (A : DGCategoryModel.{u,v,w} k) : Set (RightDGModuleModel A) :=
  Set.range (evalWrittenCode A)

/-- A small type of the written objects. Codes for the very same module are
identified, so its interpretation in right dg modules is injective. -/
abbrev WrittenObject (A : DGCategoryModel.{u,v,w} k) :=
  Quotient (Setoid.ker (evalWrittenCode A))

def writtenModule (A : DGCategoryModel.{u,v,w} k) (X : WrittenObject A) :
    RightDGModuleModel A :=
  Quotient.lift (evalWrittenCode A) (fun _ _ h => h) X

/-- The full dg subcategory on the written objects. The morphism complexes,
identities and composition are the restrictions of those in right dg modules. -/
@[reducible] def pretr (A : DGCategoryModel.{u,v,w} k) :
    DGCategoryModel.{u,max v w,max v w} k where
  Obj := WrittenObject A
  toData := (dgModuleCategory A).toData.reindex (writtenModule A)

@[reducible] def pretrInclusion (A : DGCategoryModel.{u,v,w} k) :
    DGFunctorModel (pretr A) (dgModuleCategory A) where
  obj := writtenModule A
  map _ _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

/-- The base-stage code of a representable, viewed as an object of pretr A. -/
def pretrRepresentable (A : DGCategoryModel.{u,v,w} k) (a : A.Obj) : (pretr A).Obj :=
  Quotient.mk _ ⟨0, Sum.inl ⟨a⟩⟩

structure WrittenObjectsLaws (A : DGCategoryModel.{u,v,w} k) : Prop where
  injective : Function.Injective (writtenModule A)
  range_eq : Set.range (writtenModule A) = writtenSet A
  yoneda : ∀ a, writtenModule A (pretrRepresentable A a) = representable a
  zero : zeroModule A ∈ writtenSet A
  shift : ∀ {M}, M ∈ writtenSet A → ∀ s, ShiftCone.shift M s ∈ writtenSet A
  sum : ∀ {n : ℕ} (F : Fin n → RightDGModuleModel A),
    (∀ i, F i ∈ writtenSet A) → finiteSum F ∈ writtenSet A
  cone : ∀ {P Q}, P ∈ writtenSet A → Q ∈ writtenSet A →
    ∀ (f : P ⟶ Q), ShiftCone.cone f ∈ writtenSet A
  finiteCell : ∀ X : (pretr A).Obj, SemiFree.finiteCell (writtenModule A X)
  represents : ∀ M : RightDGModuleModel A, SemiFree.finiteCell M →
    ∃ X : (pretr A).Obj, Nonempty (writtenModule A X ≅ M)

def WrittenObjects : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k), WrittenObjectsLaws A

/-- Closure and strict representatives for the canonical finite-cell predicate.
An existing finite sum may use any index universe. -/
structure CanonicalFiniteCellLaws (A : DGCategoryModel.{u,v,w} k) : Prop where
  concrete (M : RightDGModuleModel A) :
    IndexedSemiFree.finiteCell M ↔ SemiFree.finiteCell M
  zero : IndexedSemiFree.finiteCell (zeroModule A)
  representable (a : A.Obj) : IndexedSemiFree.finiteCell (representable a)
  shift {M : RightDGModuleModel A} (s : ℤ) :
    IndexedSemiFree.finiteCell M → IndexedSemiFree.finiteCell (ShiftCone.shift M s)
  sum {I : Type j} [Finite I] (F : I → RightDGModuleModel A) (S : RightDGModuleModel A)
      (D : IndexedSemiFree.StrictSum F S) :
    (∀ i, IndexedSemiFree.finiteCell (F i)) → IndexedSemiFree.finiteCell S
  cone {P Q : RightDGModuleModel A} (f : P ⟶ Q) :
    IndexedSemiFree.finiteCell P → IndexedSemiFree.finiteCell Q →
      IndexedSemiFree.finiteCell (ShiftCone.cone f)
  finiteCell (X : WrittenObject A) : IndexedSemiFree.finiteCell (writtenModule A X)
  represents (M : RightDGModuleModel A) : IndexedSemiFree.finiteCell M →
    ∃ X : WrittenObject A, Nonempty (writtenModule A X ≅ M)

def CanonicalFiniteCells : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    CanonicalFiniteCellLaws.{u,v,w,j} A

/-- Arbitrarily indexed finite sums are isomorphic to written finite sums.
In the ambient module category this is a strict dg isomorphism. -/
def WrittenFiniteSum : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type v} [Finite I] (F : I → (pretr A).Obj),
    ∃ X : (pretr A).Obj, Nonempty (writtenModule A X ≅ directSum (writtenModule A ∘ F))

/-- The enriched Yoneda functor factors through the full written subcategory. -/
def YonedaFactorization : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ E : Yoneda.EvaluationFamily A, Yoneda.EvaluationLaws E ∧
      ∃ F : DGFunctorModel (Yoneda.liftCategory A) (pretr A),
        F.obj = pretrRepresentable A ∧
        (∀ a b, HEq (F.map a b) (E a (representable b)).inv) ∧
        (∀ a b, IsIso (F.map a b))

open CoefficientLift (liftCategory liftModule liftMap)
open HomComplex (ofStrict)

/-- Interpret the original written objects over the same objects of the base
dg category with enlarged coefficients. In particular, taking `t = w` gives
the bound `max v w` for coefficients. -/
abbrev liftedWrittenModule (A : DGCategoryModel.{u,v,w} k) (X : WrittenObject A) :=
  liftModule.{u,v,w,t} (writtenModule A X)

/-- The full dg category on the chosen coefficient lifts. -/
@[reducible] def liftedPretr (A : DGCategoryModel.{u,v,w} k) :
    DGCategoryModel.{u,max v w t,max v w} k where
  Obj := WrittenObject A
  toData := (dgModuleCategory (liftCategory.{u,v,w,t} A)).toData.reindex
    (liftedWrittenModule A)

/-- The source of the comparison has the original written objects and the
coefficient lifts of their original Hom complexes. -/
abbrev sourcePretr (A : DGCategoryModel.{u,v,w} k) :=
  liftCategory.{u,max v w,max v w,t} (pretr A)

/-- A dg comparison with fixed object map. Its Hom isomorphisms conjugate each
homogeneous coefficient by the actual degreewise up and down equivalences. -/
structure LiftedHullComparison (A : DGCategoryModel.{u,v,w} k) where
  homIso (X Y : WrittenObject A) :
    (sourcePretr.{u,v,w,t} A).hom X Y ≅ (liftedPretr.{u,v,w,t} A).hom X Y
  component (X Y : WrittenObject A) (r : ℤ) (f : ((pretr A).hom X Y).X r)
      (a : A.Obj) (i q : ℤ) (h : i+r = q) (x : ((writtenModule A X).complex a).X i) :
    (HomComplex.component (((homIso X Y).hom.f r) (ULift.up f)) a i q h (ULift.up x)).down =
      HomComplex.component f a i q h x
  identity (X : WrittenObject A) :
    (homIso X X).hom.f 0 ((sourcePretr.{u,v,w,t} A).id X) = (liftedPretr.{u,v,w,t} A).id X
  composition {X Y Z : WrittenObject A} (i j n : ℤ) (h : i+j = n)
      (f : ((sourcePretr.{u,v,w,t} A).hom Y Z).X i)
      (g : ((sourcePretr.{u,v,w,t} A).hom X Y).X j) :
    (homIso X Z).hom.f n ((sourcePretr.{u,v,w,t} A).comp i j n h f g) =
      (liftedPretr.{u,v,w,t} A).comp i j n h ((homIso Y Z).hom.f i f) ((homIso X Y).hom.f j g)
  strictMap {X Y : WrittenObject A} (f : writtenModule A X ⟶ writtenModule A Y) :
    (homIso X Y).hom.f 0 (ULift.up (ofStrict f)) = ofStrict (liftMap.{u,v,w,t} f)

/-- The comparison is a dg functor, identity on the chosen objects. -/
def LiftedHullComparison.toDGFunctor {A : DGCategoryModel.{u,v,w} k}
    (E : LiftedHullComparison.{u,v,w,t} A) :
    DGFunctorModel (sourcePretr.{u,v,w,t} A) (liftedPretr.{u,v,w,t} A) where
  obj := id
  map X Y := (E.homIso X Y).hom
  map_id := E.identity
  map_comp := E.composition

structure LiftedHullLaws (A : DGCategoryModel.{u,v,w} k) : Prop where
  comparison : Nonempty (LiftedHullComparison.{u,v,w,t} A)
  yoneda (a : A.Obj) :
    liftedWrittenModule.{u,v,w,t} A (pretrRepresentable A a) =
      Yoneda.representable (A := liftCategory.{u,v,w,t} A) a
  represents (L : RightDGModuleModel (liftCategory.{u,v,w,t} A)) :
    IndexedSemiFree.finiteCell L ↔
      ∃ X : WrittenObject A, Nonempty (liftedWrittenModule.{u,v,w,t} A X ≅ L)
  isomorphism (X Y : WrittenObject A) :
    Nonempty (writtenModule A X ≅ writtenModule A Y) ↔
      Nonempty (liftedWrittenModule.{u,v,w,t} A X ≅ liftedWrittenModule.{u,v,w,t} A Y)

def LiftedHull : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k), LiftedHullLaws.{u,v,w,t} A

set_option linter.checkUnivs false in
def PretrType :=
  ∀ {k : Type u} [CommRing k] (_A : DGCategoryModel.{u,v,w} k),
    DGCategoryModel.{u,max v w,max v w} k

set_option linter.checkUnivs false in
def PretrInclusionType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    DGFunctorModel (pretr A) (dgModuleCategory A)

end
end Specs.DerivedFormalization.DG.FiniteCellConstructions
