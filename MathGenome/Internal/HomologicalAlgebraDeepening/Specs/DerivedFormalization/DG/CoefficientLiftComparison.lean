import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Derived
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

open CategoryTheory HomologicalComplex
open _root_.DerivedFormalization

universe u v w t s

namespace Specs.DerivedFormalization.DG.CoefficientLiftComparison

open CoefficientLift

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M N P : RightDGModuleModel A}

abbrev complexLift (k : Type u) [CommRing k] :
    ModuleCochain.{u,v} k ⥤ ModuleCochain.{u,max v t} k :=
  (ModuleCat.uliftFunctor.{t,v} k).mapHomologicalComplex (ComplexShape.up ℤ)

abbrev CUp (C : ModuleCochain.{u,v} k) := (complexLift.{u,v,t} k).obj C
abbrev AUp (A : DGCategoryModel.{u,v,w} k) := liftCategory.{u,v,w,t} A
abbrev MUp (M : RightDGModuleModel A) := liftModule.{u,v,w,t} M
abbrev fUp (f : M ⟶ N) := liftMap.{u,v,w,t} f

/-- The degreewise identification is linear over the original base ring. -/
abbrev termDown (C : ModuleCochain.{u,v} k) (i : ℤ) :
    (CUp.{u,v,t} C).X i ≃ₗ[k] C.X i :=
  ULift.moduleEquiv

structure ComponentLaws (A : DGCategoryModel.{u,v,w} k) : Prop where
  differential (C : ModuleCochain.{u,v} k) (i j : ℤ) (x : (CUp.{u,v,t} C).X i) :
    termDown C j ((CUp.{u,v,t} C).d i j x) = C.d i j (termDown C i x)
  identity (a : A.Obj) :
    termDown (A.hom a a) 0 ((AUp.{u,v,w,t} A).id a) = A.id a
  composition {a b c : A.Obj} (i j n : ℤ) (h : i+j = n)
      (x : ((AUp.{u,v,w,t} A).hom b c).X i) (y : ((AUp.{u,v,w,t} A).hom a b).X j) :
    termDown (A.hom a c) n ((AUp.{u,v,w,t} A).comp i j n h x y) =
      A.comp i j n h (termDown (A.hom b c) i x) (termDown (A.hom a b) j y)
  action (M : RightDGModuleModel A) {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
      (x : ((MUp.{u,v,w,t} M).complex b).X i) (y : ((AUp.{u,v,w,t} A).hom a b).X j) :
    termDown (M.complex a) n ((MUp.{u,v,w,t} M).act i j n h x y) =
      M.act i j n h (termDown (M.complex b) i x) (termDown (A.hom a b) j y)
  strictMap {M N : RightDGModuleModel A} (f : M ⟶ N) (a : A.Obj) (i : ℤ)
      (x : ((MUp.{u,v,w,t} M).complex a).X i) :
    termDown (N.complex a) i (((fUp.{u,v,w,t} f).app a).f i x) =
      (f.app a).f i (termDown (M.complex a) i x)

def ComponentComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k), ComponentLaws.{u,v,w,t} A

structure CycleBoundaryLaws (C : ModuleCochain.{u,v} k) : Prop where
  cycles (i j : ℤ) (x : (CUp.{u,v,t} C).X i) :
    (CUp.{u,v,t} C).d i j x = 0 ↔ C.d i j (termDown C i x) = 0
  boundaries (i j : ℤ) (y : (CUp.{u,v,t} C).X j) :
    (∃ x, (CUp.{u,v,t} C).d i j x = y) ↔ ∃ x, C.d i j x = termDown C j y

def CycleBoundaryComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (C : ModuleCochain.{u,v} k), CycleBoundaryLaws.{u,v,t} C

/-- Canonical homology comparison from the exact module lift. -/
noncomputable def homologyIso (C : ModuleCochain.{u,v} k) (i : ℤ) :
    (CUp.{u,v,t} C).homology i ≅ (ModuleCat.uliftFunctor.{t,v} k).obj (C.homology i) :=
  (C.sc i).mapHomologyIso (ModuleCat.uliftFunctor.{t,v} k)

/-- Canonical cycles comparison, compatible with the inclusion into the terms. -/
noncomputable def cyclesIso (C : ModuleCochain.{u,v} k) (i : ℤ) :
    (CUp.{u,v,t} C).cycles i ≅ (ModuleCat.uliftFunctor.{t,v} k).obj (C.cycles i) :=
  (C.sc i).mapCyclesIso (ModuleCat.uliftFunctor.{t,v} k)

def HomologyComparison : Prop :=
  ∀ {k : Type u} [CommRing k],
    let U := ModuleCat.uliftFunctor.{t,v} k
    (∀ (C : ModuleCochain.{u,v} k) (i : ℤ),
      (cyclesIso.{u,v,t} C i).hom ≫ U.map (C.iCycles i) = (CUp.{u,v,t} C).iCycles i ∧
      (cyclesIso.{u,v,t} C i).hom ≫ U.map (C.homologyπ i) =
        (CUp.{u,v,t} C).homologyπ i ≫ (homologyIso.{u,v,t} C i).hom) ∧
    (∀ {C D : ModuleCochain.{u,v} k} (f : C ⟶ D) (i : ℤ),
      homologyMap ((complexLift.{u,v,t} k).map f) i ≫ (homologyIso.{u,v,t} D i).hom =
        (homologyIso.{u,v,t} C i).hom ≫ U.map (homologyMap f i))

abbrev DegreewiseInjective (f : M ⟶ N) := ∀ a i, Function.Injective ((f.app a).f i)

def MapProperties : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (M N : RightDGModuleModel A),
    (Module.acyclic (MUp.{u,v,w,t} M) ↔ Module.acyclic M) ∧
    ∀ (f : M ⟶ N),
      (DegreewiseInjective (fUp.{u,v,w,t} f) ↔ DegreewiseInjective f) ∧
      (Module.degreewiseSurjective (fUp.{u,v,w,t} f) ↔ Module.degreewiseSurjective f) ∧
      (Module.quasiIsomorphism (fUp.{u,v,w,t} f) ↔ Module.quasiIsomorphism f)

variable {L : RightDGModuleModel (AUp.{u,v,w,t} A)}

/-- Evaluate an arbitrary enlarged map into the original coefficients of its target. -/
def evaluate (f : L ⟶ MUp.{u,v,w,t} M) (a : A.Obj) (i : ℤ) :
    (L.complex a).X i →ₗ[k] (M.complex a).X i :=
  (termDown (M.complex a) i).toLinearMap.comp ((f.app a).f i).hom

/-- On actual cohomology, use the canonical comparison after the homology map. -/
noncomputable def evaluateHomology (f : L ⟶ MUp.{u,v,w,t} M) (a : A.Obj) (i : ℤ) :
    (L.complex a).homology i →ₗ[k] (M.complex a).homology i :=
  ULift.moduleEquiv.toLinearMap.comp
    ((homologyMap (f.app a) i ≫ (homologyIso.{u,v,t} (M.complex a) i).hom).hom)

/-- On cycles, use the comparison with the original kernel of the differential. -/
noncomputable def evaluateCycles (f : L ⟶ MUp.{u,v,w,t} M) (a : A.Obj) (i : ℤ) :
    (L.complex a).cycles i →ₗ[k] (M.complex a).cycles i :=
  ULift.moduleEquiv.toLinearMap.comp
    ((cyclesMap (f.app a) i ≫ (cyclesIso.{u,v,t} (M.complex a) i).hom).hom)

structure EvaluationLaws (f : L ⟶ MUp.{u,v,w,t} M) : Prop where
  differential (a : A.Obj) (i j : ℤ) (x : (L.complex a).X i) :
    evaluate f a j ((L.complex a).d i j x) = (M.complex a).d i j (evaluate f a i x)
  action {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
      (x : (L.complex b).X i) (z : (A.hom a b).X j) :
    evaluate f a n (L.act i j n h x (ULift.up z)) =
      M.act i j n h (evaluate f b i x) z
  cycles (a : A.Obj) (i : ℤ) (x : (L.complex a).cycles i) :
    evaluate f a i ((L.complex a).iCycles i x) =
      (M.complex a).iCycles i (evaluateCycles f a i x)
  homology (a : A.Obj) (i : ℤ) (x : (L.complex a).cycles i) :
    evaluateHomology f a i ((L.complex a).homologyπ i x) =
      (M.complex a).homologyπ i (evaluateCycles f a i x)
  surjective (a : A.Obj) (i : ℤ) :
    Function.Surjective (evaluate f a i) ↔ Function.Surjective ((f.app a).f i)
  bijectiveHomology (a : A.Obj) (i : ℤ) :
    Function.Bijective (evaluateHomology f a i) ↔ IsIso (homologyMap (f.app a) i)

def Evaluation : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} {L : RightDGModuleModel (AUp.{u,v,w,t} A)}
    (f : L ⟶ MUp.{u,v,w,t} M), EvaluationLaws f

open HomComplex (gradedHom homComplex component ofStrict compose homotopyCategory homotopyClass)
open Basic (classOf h0Hom cyclesZero)

abbrev GradedComparisonFamily (M N : RightDGModuleModel A) :=
  ∀ r, gradedHom M N r ≃ₗ[k] gradedHom (MUp.{u,v,w,t} M) (MUp.{u,v,w,t} N) r

structure GradedLaws (A : DGCategoryModel.{u,v,w} k)
    (E : ∀ M N : RightDGModuleModel A, GradedComparisonFamily.{u,v,w,t} M N) : Prop where
  component {M N : RightDGModuleModel A} (r : ℤ) (f : gradedHom M N r)
      (a : A.Obj) (i j : ℤ) (h : i+r = j) (x : (M.complex a).X i) :
    (HomComplex.component (E M N r f) a i j h (ULift.up x)).down =
      HomComplex.component f a i j h x
  differential {M N : RightDGModuleModel A} (r q : ℤ) (f : gradedHom M N r) :
    E M N q ((homComplex M N).d r q f) =
      (homComplex (MUp.{u,v,w,t} M) (MUp.{u,v,w,t} N)).d r q (E M N r f)
  composition {M N P : RightDGModuleModel A} (s r n : ℤ) (h : s+r = n)
      (g : gradedHom N P s) (f : gradedHom M N r) :
    E M P n (compose M N P s r n h g f) =
      compose _ _ _ s r n h (E N P s g) (E M N r f)
  strictMap {M N : RightDGModuleModel A} (f : M ⟶ N) :
    E M N 0 (ofStrict f) = ofStrict (fUp.{u,v,w,t} f)
  yoneda (a : A.Obj) {M : RightDGModuleModel A} (r : ℤ)
      (f : gradedHom (Yoneda.representable a) M r) :
    (HomComplex.component (E (Yoneda.representable a) M r f) a 0 r (zero_add r)
      ((AUp.{u,v,w,t} A).id a)).down = HomComplex.component f a 0 r (zero_add r) (A.id a)

def GradedComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ E : ∀ M N : RightDGModuleModel A, GradedComparisonFamily.{u,v,w,t} M N, GradedLaws A E

def HomotopyComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
      {M N : RightDGModuleModel A} (f g : M ⟶ N),
    homotopyClass (fUp.{u,v,w,t} f) = homotopyClass (fUp.{u,v,w,t} g) ↔
      homotopyClass f = homotopyClass g

def StrictFullFaithfulness : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    Nonempty (liftFunctor.{u,v,w,t} A).FullyFaithful

noncomputable def HomotopyAndDerivedComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws A) (h' : Derived.HomotopyCategoryLaws (AUp.{u,v,w,t} A)),
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory (AUp.{u,v,w,t} A) h'
    letI : Category (Derived.derivedCategory A h) :=
      inferInstanceAs (Category (@MorphismProperty.Localization _
        (Derived.homotopyCategory A h) (Derived.quasiIsomorphisms A)))
    letI : Category (Derived.derivedCategory (AUp.{u,v,w,t} A) h') :=
      inferInstanceAs (Category (@MorphismProperty.Localization _
        (Derived.homotopyCategory (AUp.{u,v,w,t} A) h') (Derived.quasiIsomorphisms (AUp.{u,v,w,t} A))))
    ∃ F : homotopyCategory A ⥤ homotopyCategory (AUp.{u,v,w,t} A),
      Nonempty F.FullyFaithful ∧
      (∀ (M : RightDGModuleModel A), F.obj M = MUp.{u,v,w,t} M) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        HEq (F.map (homotopyClass f)) (homotopyClass (fUp.{u,v,w,t} f))) ∧
      ∃ G : Derived.derivedCategory A h ⥤ Derived.derivedCategory (AUp.{u,v,w,t} A) h',
        Nonempty (Derived.quotient A h ⋙ G ≅ F ⋙ Derived.quotient (AUp.{u,v,w,t} A) h')

open ShiftCone (shift shiftMap cone coneInclusion coneProjection)
open CategoryTheory.Limits (IsZero)

/-- The original representables have precisely the lifted arrow complexes and actions. -/
def RepresentableComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k) (a : A.Obj),
    MUp.{u,v,w,t} (Yoneda.representable a) = Yoneda.representable (A := AUp.{u,v,w,t} A) a

def ZeroComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (Z : RightDGModuleModel A),
    IsZero Z ↔ IsZero (MUp.{u,v,w,t} Z)

def ShiftComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (s : ℤ),
    ∃ E : ∀ M : RightDGModuleModel A, MUp.{u,v,w,t} (shift M s) ≅ shift (MUp.{u,v,w,t} M) s,
      (∀ (M : RightDGModuleModel A) (a : A.Obj) (i : ℤ)
          (x : ((MUp.{u,v,w,t} (shift M s)).complex a).X i),
        ((E M).hom.app a |>.f i |>.hom x).down = x.down) ∧
      ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        fUp.{u,v,w,t} (shiftMap s f) ≫ (E N).hom =
          (E M).hom ≫ shiftMap s (fUp.{u,v,w,t} f)

/-- The map of the concrete cones induced by a commuting square. -/
def coneMap {M N M' N' : RightDGModuleModel A} {f : M ⟶ N} {g : M' ⟶ N'}
    (p : M ⟶ M') (q : N ⟶ N') (h : f ≫ q = p ≫ g) : cone f ⟶ cone g where
  app a := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom (((q.app a).f i).hom.prodMap ((p.app a).f (i+1)).hom))
    (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ShiftCone.coneDiff g a i (i+1) ((q.app a).f i x.1, (p.app a).f (i+1) x.2) =
        ((q.app a).f (i+1) (ShiftCone.coneDiff f a i (i+1) x).1,
          (p.app a).f (i+1+1) (ShiftCone.coneDiff f a i (i+1) x).2)
      rw [ShiftCone.coneDiff_succ, ShiftCone.coneDiff_succ]
      apply Prod.ext
      · change (N'.complex a).d i (i+1) ((q.app a).f i x.1) +
          (g.app a).f (i+1) ((p.app a).f (i+1) x.2) =
          (q.app a).f (i+1) ((N.complex a).d i (i+1) x.1 + (f.app a).f (i+1) x.2)
        rw [map_add]
        congr 1
        · exact CategoryTheory.congr_fun ((q.app a).comm i (i+1)) x.1
        · exact (CategoryTheory.congr_fun
            (congrArg (fun m : M ⟶ N' => (m.app a).f (i+1)) h) x.2).symm
      · change -(M'.complex a).d (i+1) (i+1+1) ((p.app a).f (i+1) x.2) =
          (p.app a).f (i+1+1) (-(M.complex a).d (i+1) (i+1+1) x.2)
        rw [map_neg]
        exact congrArg Neg.neg (CategoryTheory.congr_fun ((p.app a).comm (i+1) (i+1+1)) x.2))
  comm_act := by
    intro a b i j n h' x z
    exact Prod.ext (q.comm_act i j n h' x.1 z)
      (p.comm_act (i+1) j (n+1) (by omega) x.2 z)

/-- The cone comparison preserves the inclusion, projection, and maps of squares. -/
def ConeComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    ∃ S : ∀ M : RightDGModuleModel A, MUp.{u,v,w,t} (shift M 1) ≅ shift (MUp.{u,v,w,t} M) 1,
      (∀ (M : RightDGModuleModel A) (a : A.Obj) (i : ℤ)
          (x : ((MUp.{u,v,w,t} (shift M 1)).complex a).X i),
        ((S M).hom.app a |>.f i |>.hom x).down = x.down) ∧
    ∃ E : ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
      MUp.{u,v,w,t} (cone f) ≅ cone (fUp.{u,v,w,t} f),
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N) (a : A.Obj) (i : ℤ)
          (x : ((MUp.{u,v,w,t} (cone f)).complex a).X i),
        ((E f).hom.app a |>.f i |>.hom x) = (ULift.up x.down.1, ULift.up x.down.2)) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        fUp.{u,v,w,t} (coneInclusion f) ≫ (E f).hom = coneInclusion (fUp.{u,v,w,t} f) ∧
        fUp.{u,v,w,t} (coneProjection f) ≫ (S M).hom = (E f).hom ≫ coneProjection (fUp.{u,v,w,t} f)) ∧
      ∀ {M N M' N' : RightDGModuleModel A} {f : M ⟶ N} {g : M' ⟶ N'}
        (p : M ⟶ M') (q : N ⟶ N') (h : f ≫ q = p ≫ g),
        fUp.{u,v,w,t} (coneMap p q h) ≫ (E g).hom =
          (E f).hom ≫ coneMap (fUp.{u,v,w,t} p) (fUp.{u,v,w,t} q) (by
            change (liftFunctor.{u,v,w,t} A).map f ≫ (liftFunctor.{u,v,w,t} A).map q =
              (liftFunctor.{u,v,w,t} A).map p ≫ (liftFunctor.{u,v,w,t} A).map g
            rw [← Functor.map_comp, ← Functor.map_comp, h])

section Restriction

variable {B : DGCategoryModel.{u,v,w} k}

/-- Pull a right action back along a dg functor without changing the term complexes. -/
@[reducible] def restrictModule (F : DGFunctorModel A B) (M : RightDGModuleModel B) :
    RightDGModuleModel A where
  complex a := M.complex (F.obj a)
  act {a b} i j n h :=
    (LinearMap.lcomp k _ ((F.map a b).f j).hom).comp
      (M.act (a := F.obj a) (b := F.obj b) i j n h)
  act_id a i x := by
    change M.act i 0 i _ x ((F.map a a).f 0 (A.id a)) = x
    rw [F.map_id, M.act_id]
  act_assoc {a b c} i j l x y z := by
    change M.act (i+j) l (i+j+l) _ (M.act i j (i+j) _ x ((F.map b c).f j y))
        ((F.map a b).f l z) = M.act i (j+l) (i+j+l) _ x ((F.map a c).f (j+l) (A.comp j l (j+l) _ y z))
    rw [F.map_comp, M.act_assoc]
  leibniz {a b} i j n h x z := by
    change (M.complex (F.obj a)).d n (n+1) (M.act i j n h x ((F.map a b).f j z)) =
      M.act (i+1) j (n+1) _ ((M.complex (F.obj b)).d i (i+1) x) ((F.map a b).f j z) +
        i.negOnePow • M.act i (j+1) (n+1) _ x ((F.map a b).f (j+1) ((A.hom a b).d j (j+1) z))
    have hz := CategoryTheory.congr_fun ((F.map a b).comm j (j+1)) z
    simp only [ModuleCat.comp_apply] at hz
    rw [M.leibniz, hz]

@[reducible] def restrictMap (F : DGFunctorModel A B) {M N : RightDGModuleModel B} (f : M ⟶ N) :
    restrictModule F M ⟶ restrictModule F N where
  app a := f.app (F.obj a)
  comm_act {a b} i j n h x z := f.comm_act i j n h x ((F.map a b).f j z)

end Restriction

set_option linter.checkUnivs false in
/-- Successive lifts and the one-step lift have the same coefficients via flattening. -/
abbrev doubleCategory (A : DGCategoryModel.{u,v,w} k) :=
  AUp.{u,max v t,w,s} (AUp.{u,v,w,t} A)

abbrev doubleModule (M : RightDGModuleModel A) :=
  MUp.{u,max v t,w,s} (MUp.{u,v,w,t} M)

abbrev doubleMap (f : M ⟶ N) :=
  fUp.{u,max v t,w,s} (fUp.{u,v,w,t} f)

def SuccessiveComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ F : DGFunctorModel (doubleCategory.{u,v,w,t,s} A) (AUp.{u,v,w,max t s} A),
      ∃ _h : F.obj = id,
        (∀ a b, IsIso (F.map a b)) ∧
        (∀ (a b : A.Obj) (i : ℤ) (z : ((doubleCategory.{u,v,w,t,s} A).hom a b).X i),
          HEq ((F.map a b).f i z) (ULift.up.{max t s} z.down.down)) ∧
        ∃ E : ∀ M : RightDGModuleModel A,
          doubleModule.{u,v,w,t,s} M ≅ restrictModule F (MUp.{u,v,w,max t s} M),
          (∀ (M : RightDGModuleModel A) (a : A.Obj) (i : ℤ)
              (x : ((doubleModule.{u,v,w,t,s} M).complex a).X i),
            HEq ((E M).hom.app a |>.f i |>.hom x) (ULift.up.{max t s} x.down.down)) ∧
          ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
            doubleMap.{u,v,w,t,s} f ≫ (E N).hom = (E M).hom ≫ restrictMap F (fUp.{u,v,w,max t s} f)

/-- In an unchanged universe the comparison sends each lifted term back down. -/
def SameUniverseComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v t,w} k),
    ∃ F : DGFunctorModel (AUp.{u,max v t,w,t} A) A,
      ∃ _h : F.obj = id,
        (∀ a b, IsIso (F.map a b)) ∧
        (∀ (a b : A.Obj) (i : ℤ) (z : ((AUp.{u,max v t,w,t} A).hom a b).X i),
          HEq ((F.map a b).f i z) z.down) ∧
        ∃ E : ∀ M : RightDGModuleModel A,
          MUp.{u,max v t,w,t} M ≅ restrictModule F M,
          (∀ (M : RightDGModuleModel A) (a : A.Obj) (i : ℤ)
              (x : ((MUp.{u,max v t,w,t} M).complex a).X i),
            HEq ((E M).hom.app a |>.f i |>.hom x) x.down) ∧
          ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
            fUp.{u,max v t,w,t} f ≫ (E N).hom = (E M).hom ≫ restrictMap F f

/-- The degree-zero cohomology of the graded Hom comparison is linear over the base ring. -/
def H0LinearComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
      (M N : RightDGModuleModel A),
    ∃ E : h0Hom (homComplex M N) ≃ₗ[k]
      h0Hom (homComplex (MUp.{u,v,w,t} M) (MUp.{u,v,w,t} N)),
      ∀ (f : M ⟶ N), E (homotopyClass f) = homotopyClass (fUp.{u,v,w,t} f)

end Specs.DerivedFormalization.DG.CoefficientLiftComparison
