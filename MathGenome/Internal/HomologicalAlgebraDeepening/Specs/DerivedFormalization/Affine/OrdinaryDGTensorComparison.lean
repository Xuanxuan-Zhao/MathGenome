import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectHomBaseChange

open CategoryTheory
open scoped TensorProduct
open _root_.DerivedFormalization _root_.DerivedFormalization.Affine

namespace Specs.DerivedFormalization.Affine.OrdinaryDGTensorComparison

noncomputable section

set_option autoImplicit false

universe u v t

open Cochains (compValue)
open CochainModels (isKProjectiveValue)
open CotangentComplex (liftCDGA cdgaLift)
open Tensor (ModuleTensor dgCat term act regular)
open DG.Derived (HomotopyCategoryLaws quotient)
open DG.DerivedKProjective (derivedCategoryInstance kProjectiveObjects restrictedLocalization)
open DG.HomComplex (homotopyClass)
open DG.KProjective (isKProjective)
open Descent.PerfectHomBaseChange (extend extendId extendComp)

variable {k : Type u} [Field k] [CharZero k]
variable {R S V : Type v} [CommRing R] [CommRing S] [CommRing V]
variable [Algebra k R] [Algebra k S] [Algebra k V]

/-- The degree-zero algebra in the A08 coefficient lift of the original stalk. -/
abbrev transported (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] : CommDGAlgebra.{u,max v t} k :=
  (liftCDGA.{u,v,t} (NonpositiveCDGA.ordinary (CommAlgCat.of k R))).toCommDGAlgebra

/-- The actual transported morphism of stalks, using the given ring map. -/
abbrev transportedMap (f : R →ₐ[k] S) :
    transported.{u,v,t} k R ⟶ transported.{u,v,t} k S :=
  (cdgaLift.{u,v,t} k).map (NonpositiveCDGA.ordinaryMap (CommAlgCat.ofHom f))

abbrev restriction (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R] :=
  (ModuleCat.restrictScalars.{max v t} (algebraMap k R)).mapHomologicalComplex (.up ℤ)

local instance transportedRing : CommRing (transported.{u,v,t} k R).DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero (transported.{u,v,t} k R)

local instance transportedAlgebra : Algebra k (transported.{u,v,t} k R).DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero (transported.{u,v,t} k R)

/-- Strict input data on the one-object category. The term isomorphisms
identify the scalar actions through the original ring. -/
structure StrictComparison (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] where
  scalar : R ≃ₐ[k] (transported.{u,v,t} k R).DegreeZero
  scalar_apply (r : R) : scalar r = ULift.up r
  strict : compValue.{max v t} R ⥤ (transported.{u,v,t} k R).Module
  terms (X : compValue.{max v t} R) :
    (restriction.{u,v,t} k R).obj X ≅ (strict.obj X).complex ()
  terms_natural {X Y : compValue.{max v t} R} (a : X ⟶ Y) :
    (restriction.{u,v,t} k R).map a ≫ (terms Y).hom =
      (terms X).hom ≫ (strict.map a).app ()
  action (X : compValue.{max v t} R) (i : ℤ) (r : R) (x : X.X i) :
    act (strict.obj X) i 0 i (add_zero i) ((terms X).hom.f i x) (scalar r) =
      (terms X).hom.f i (r • x)

def StrictComparison.PreservesKProjectives (E : StrictComparison.{u,v,t} k R) : Prop :=
  ∀ X : compValue.{max v t} R, isKProjectiveValue X → isKProjective (E.strict.obj X)

variable (E : StrictComparison.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k)

abbrev TensorComparison :=
  ∀ X Y : compValue.{max v t} R, E.strict.obj (CochainTensor.tensor X Y) ≅
    T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y)

def TensorComparison.OnPure (e : TensorComparison E T) : Prop :=
  ∀ (X Y : compValue.{max v t} R) (i j n : ℤ) (h : i+j=n) (x : X.X i) (y : Y.X j),
    ((e X Y).hom.app ()).f n ((E.terms (CochainTensor.tensor X Y)).hom.f n
      (CochainTensor.pure X Y h x y)) =
      T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h ((E.terms X).hom.f i x) ((E.terms Y).hom.f j y)

/-- The native ordinary model of U01AdequateModels has the same generator
after the ring equivalence, before the comparison with the signed dg model. -/
def TensorComparison.OnRepresentedPure (e : TensorComparison E T)
    (U : CochainTensorTransport.AdequateModel E.scalar.toRingEquiv) : Prop :=
  let F := CochainRingTransport.complexFunctorValue E.scalar.toRingEquiv
  ∀ (X Y : compValue.{max v t} R) (i j n : ℤ) (h : i+j=n) (x : X.X i) (y : Y.X j),
    ((e X Y).hom.app ()).f n ((E.terms (CochainTensor.tensor X Y)).hom.f n
      ((U.tensorIso X Y).hom.f n (CochainTensor.pure (F.obj X) (F.obj Y) h x y))) =
      T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h ((E.terms X).hom.f i x) ((E.terms Y).hom.f j y)

/-- The square uses the strict tensor map characterized by its action on
homogeneous generators in both variables. -/
def TensorComparison.Natural (e : TensorComparison E T) : Prop :=
  ∀ {X X' Y Y' : compValue.{max v t} R} (a : X ⟶ X') (b : Y ⟶ Y')
    (c : T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y) ⟶
         T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X') (E.strict.obj Y')),
    (∀ (i j n : ℤ) (h : i+j=n) (x : term (E.strict.obj X) i) (y : term (E.strict.obj Y) j),
      (c.app ()).f n (T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h x y) =
        T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h ((E.strict.map a).app () |>.f i x)
          ((E.strict.map b).app () |>.f j y)) →
    E.strict.map (CochainTensor.map a b) ≫ (e X' Y').hom = (e X Y).hom ≫ c

def InternalTensor : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {R : Type v} [CommRing R] [Algebra k R],
  ∀ (E : StrictComparison.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k)
    (U : CochainTensorTransport.AdequateModel E.scalar.toRingEquiv),
    (∀ N : (transported.{u,v,t} k R).Module, T.Formulas (𝟙 (transported.{u,v,t} k R)) N) →
    ∃ e : TensorComparison E T, e.OnPure E T ∧ e.OnRepresentedPure E T U ∧ e.Natural E T

/-- Localize the inverse of the very same strict comparison, preceded by
the projective-model isomorphism for ADerivedTensor. -/
def LocalizedTensor : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {R : Type v} [CommRing R] [Algebra k R],
  ∀ (E : StrictComparison.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k)
    (e : TensorComparison E T),
    (hE : E.PreservesKProjectives) → e.OnPure E T →
    ∀ (h : HomotopyCategoryLaws (dgCat (transported.{u,v,t} k R)))
      (H : DerivedTensor.HomotopyTensor T (𝟙 (transported.{u,v,t} k R)) h h),
      letI := DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k R)) h
      letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k R)) h
      let Q := quotient (dgCat (transported.{u,v,t} k R)) h
      ∀ (I : (restrictedLocalization (dgCat (transported.{u,v,t} k R)) h).IsEquivalence),
        letI := I
        let L := (restrictedLocalization (dgCat (transported.{u,v,t} k R)) h).asEquivalence
        let J := (kProjectiveObjects (dgCat (transported.{u,v,t} k R))).ι
        ∀ (X Y : compValue.{max v t} R) (hX : isKProjectiveValue X) (hY : isKProjectiveValue Y),
          let P := E.strict.obj X
          let N := E.strict.obj Y
          let P₀ : (kProjectiveObjects (dgCat (transported.{u,v,t} k R))).FullSubcategory := ⟨P, hE X hX⟩
          let N₀ : (kProjectiveObjects (dgCat (transported.{u,v,t} k R))).FullSubcategory := ⟨N, hE Y hY⟩
          let ε := ((J.mapIso (L.unitIso.app P₀)).symm).prod ((J.mapIso (L.unitIso.app N₀)).symm)
          let d := (H.functor ⋙ Q).mapIso ε ≪≫ Q.mapIso (eqToIso (H.obj P N))
          ∃ a : (DerivedTensor.derivedTensorValue T h H I).obj (Q.obj P, Q.obj N) ≅
              Q.obj (E.strict.obj (CochainTensor.tensor X Y)),
            a.hom = d.hom ≫ Q.map (homotopyClass (e X Y).inv)

variable [Algebra R S] [IsScalarTower k R S]

abbrev scalarMap (k : Type u) [Field k] [CharZero k]
    (R S : Type v) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra R S] [IsScalarTower k R S] :
    transported.{u,v,t} k R ⟶ transported.{u,v,t} k S :=
  transportedMap.{u,v,t} (IsScalarTower.toAlgHom k R S)

/-- F08a writes the degree-zero scalar first, and the right dg tensor
writes that same scalar last. -/
structure ExtensionComparison (F : StrictComparison.{u,v,t} k S) (T : ModuleTensor.{u,max v t} k) where
  iso : (extend.{v,v,max v t} R S) ⋙ F.strict ≅
    E.strict ⋙ T.baseChange (scalarMap.{u,v,t} k R S)
  on_tmul (X : compValue.{max v t} R) (i : ℤ) (s : S) (x : X.X i) :
    ((iso.hom.app X).app ()).f i ((F.terms ((extend.{v,v,max v t} R S).obj X)).hom.f i
      (s ⊗ₜ[R] x)) =
      T.tmul (scalarMap.{u,v,t} k R S) (N := regular (transported.{u,v,t} k S))
        i 0 i (add_zero i) ((E.terms X).hom.f i x) (F.scalar s)

def ScalarExtension : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra R S] [IsScalarTower k R S],
  ∀ (E : StrictComparison.{u,v,t} k R) (F : StrictComparison.{u,v,t} k S)
    (T : ModuleTensor.{u,max v t} k),
    T.Formulas (scalarMap.{u,v,t} k R S) (regular (transported.{u,v,t} k S)) →
      Nonempty (ExtensionComparison E F T)

def ScalarExtensionUnit : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {R : Type v} [CommRing R] [Algebra k R],
  ∀ (E : StrictComparison.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionComparison E E T), T.Comparisons →
    ∃ eq : scalarMap.{u,v,t} k R R = 𝟙 (transported.{u,v,t} k R),
      ∀ X : compValue.{max v t} R,
        ∃ a : (T.baseChange (𝟙 (transported.{u,v,t} k R))).obj (E.strict.obj X) ≅ E.strict.obj X,
          ((e.iso.app X).hom ≫
            eqToHom (congrArg (fun r => (T.baseChange r).obj (E.strict.obj X)) eq)) ≫ a.hom =
              E.strict.map (extendId R X).hom ∧
          ∀ (i j n : ℤ) (h : i+j=n) (x : term (E.strict.obj X) i) (r : (transported.{u,v,t} k R).complex.X j),
            (a.hom.app ()).f n (T.tmul (𝟙 (transported.{u,v,t} k R)) (N := regular (transported.{u,v,t} k R)) i j n h x r) =
              act (E.strict.obj X) i j n h x r

def LocalizedExtension : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra R S] [IsScalarTower k R S],
  ∀ (E : StrictComparison.{u,v,t} k R) (F : StrictComparison.{u,v,t} k S)
    (T : ModuleTensor.{u,max v t} k) (e : ExtensionComparison E F T)
    (hR : HomotopyCategoryLaws (dgCat (transported.{u,v,t} k R))) (hS : HomotopyCategoryLaws (dgCat (transported.{u,v,t} k S)))
    (W : DerivedTensor.ScalarExtension T (scalarMap.{u,v,t} k R S) hR hS),
    ∀ (hE : E.PreservesKProjectives),
      letI := DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k R)) hR
      letI := DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k S)) hS
      letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k R)) hR
      letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k S)) hS
      let QR := quotient (dgCat (transported.{u,v,t} k R)) hR
      let QS := quotient (dgCat (transported.{u,v,t} k S)) hS
      ∀ (P : compValue.{max v t} R) (hP : isKProjectiveValue P),
        ∃ a : W.functor.obj (QR.obj (E.strict.obj P)) ≅
            QS.obj (F.strict.obj ((extend.{v,v,max v t} R S).obj P)),
          a.hom = (W.onProjective (E.strict.obj P) (hE P hP)).hom ≫
            QS.map (homotopyClass (e.iso.inv.app P))

variable [Algebra R V] [Algebra S V] [IsScalarTower k R V] [IsScalarTower k S V]
variable [IsScalarTower R S V]

/-- The fourth side of the strict square is the canonical associator for
ordinary extension along the same tower. -/
def TowerSquare (F : StrictComparison.{u,v,t} k S) (G : StrictComparison.{u,v,t} k V)
    (e : ExtensionComparison E F T) (f : ExtensionComparison F G T) (g : ExtensionComparison E G T)
    (eq : (scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V) = (scalarMap.{u,v,t} k R V)) (X : compValue.{max v t} R)
    (a : (T.baseChange (scalarMap.{u,v,t} k S V)).obj ((T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X)) ⟶
      (T.baseChange ((scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V))).obj (E.strict.obj X)) : Prop :=
  (f.iso.app ((extend.{v,v,max v t} R S).obj X)).hom ≫
    (T.baseChange (scalarMap.{u,v,t} k S V)).map (e.iso.app X).hom ≫ a ≫
      eqToHom (congrArg (fun m => (T.baseChange m).obj (E.strict.obj X)) eq) =
    G.strict.map (extendComp.{v,v,max v t} R S V X).hom ≫ (g.iso.app X).hom

/-- The strict associator multiplies the two scalar factors. -/
def TowerOnPure (M : (transported.{u,v,t} k R).Module)
    (a : (T.baseChange (scalarMap.{u,v,t} k S V)).obj ((T.baseChange (scalarMap.{u,v,t} k R S)).obj M) ⟶
      (T.baseChange ((scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V))).obj M) : Prop :=
  ∀ (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
    (x : term M i) (s : (transported.{u,v,t} k S).complex.X j) (z : (transported.{u,v,t} k V).complex.X l),
    (a.app ()).f n
      (T.tmul (scalarMap.{u,v,t} k S V) (N := regular (transported.{u,v,t} k V)) m l n hn
        (T.tmul (scalarMap.{u,v,t} k R S) (N := regular (transported.{u,v,t} k S)) i j m hm x s) z) =
    T.tmul ((scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V)) (N := regular (transported.{u,v,t} k V)) i (j+l) n (by omega) x
      ((transported.{u,v,t} k V).mul j l (j+l) rfl ((scalarMap.{u,v,t} k S V).chainMap.f j s) z)

def ScalarExtensionTower : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {R S V : Type v} [CommRing R] [CommRing S] [CommRing V]
    [Algebra k R] [Algebra k S] [Algebra k V]
    [Algebra R S] [IsScalarTower k R S]
    [Algebra R V] [Algebra S V] [IsScalarTower k R V] [IsScalarTower k S V]
    [IsScalarTower R S V],
  ∀ (E : StrictComparison.{u,v,t} k R) (F : StrictComparison.{u,v,t} k S)
    (G : StrictComparison.{u,v,t} k V) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionComparison E F T) (f : ExtensionComparison F G T) (g : ExtensionComparison E G T),
    T.Formulas (scalarMap.{u,v,t} k S V) (regular (transported.{u,v,t} k V)) → T.Comparisons →
    ∃ eq : (scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V) = (scalarMap.{u,v,t} k R V),
      ∀ X : compValue.{max v t} R,
        ∃ a : (T.baseChange (scalarMap.{u,v,t} k S V)).obj ((T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X)) ≅
            (T.baseChange ((scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V))).obj (E.strict.obj X),
          TowerOnPure T (E.strict.obj X) a.hom ∧ TowerSquare E T F G e f g eq X a.hom

/-- The same strict associator enters the F08a tower square and the
ADerivedTensor computation of the localized tower on K-projectives. -/
def LocalizedExtensionTower : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {R S V : Type v} [CommRing R] [CommRing S] [CommRing V]
    [Algebra k R] [Algebra k S] [Algebra k V]
    [Algebra R S] [IsScalarTower k R S]
    [Algebra R V] [Algebra S V] [IsScalarTower k R V] [IsScalarTower k S V]
    [IsScalarTower R S V],
  ∀ (E : StrictComparison.{u,v,t} k R) (F : StrictComparison.{u,v,t} k S)
    (G : StrictComparison.{u,v,t} k V) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionComparison E F T) (f : ExtensionComparison F G T) (g : ExtensionComparison E G T)
    (hR : HomotopyCategoryLaws (dgCat (transported.{u,v,t} k R))) (hS : HomotopyCategoryLaws (dgCat (transported.{u,v,t} k S)))
    (hV : HomotopyCategoryLaws (dgCat (transported.{u,v,t} k V)))
    (W : DerivedTensor.ScalarExtension T (scalarMap.{u,v,t} k R S) hR hS)
    (Y : DerivedTensor.ScalarExtension T (scalarMap.{u,v,t} k S V) hS hV)
    (Z : DerivedTensor.ScalarExtension T ((scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V)) hR hV),
    T.Formulas (scalarMap.{u,v,t} k S V) (regular (transported.{u,v,t} k V)) → (hE : E.PreservesKProjectives) →
    DerivedTensor.ExtensionCompositionLaws T (scalarMap.{u,v,t} k R S) (scalarMap.{u,v,t} k S V) hR hS hV W Y Z →
      letI := DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k R)) hR
      letI := DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k S)) hS
      letI := DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k V)) hV
      letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k R)) hR
      letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k S)) hS
      letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k V)) hV
      let QR := quotient (dgCat (transported.{u,v,t} k R)) hR
      let QV := quotient (dgCat (transported.{u,v,t} k V)) hV
      ∃ (eq : (scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V) = (scalarMap.{u,v,t} k R V))
        (a : T.baseChange (scalarMap.{u,v,t} k R S) ⋙ T.baseChange (scalarMap.{u,v,t} k S V) ≅ T.baseChange ((scalarMap.{u,v,t} k R S) ≫ (scalarMap.{u,v,t} k S V)))
        (b : W.functor ⋙ Y.functor ≅ Z.functor),
        (∀ X : compValue.{max v t} R,
          TowerSquare E T F G e f g eq X (a.hom.app (E.strict.obj X))) ∧
        (∀ M : (transported.{u,v,t} k R).Module, TowerOnPure T M (a.hom.app M)) ∧
        ∀ (P : compValue.{max v t} R) (hP : isKProjectiveValue P),
          let M := E.strict.obj P
          let hM := hE P hP
          ∃ h₁ : isKProjective ((T.baseChange (scalarMap.{u,v,t} k R S)).obj M),
            b.hom.app (QR.obj M) ≫ (Z.onProjective M hM).hom =
              Y.functor.map (W.onProjective M hM).hom ≫
              (Y.onProjective ((T.baseChange (scalarMap.{u,v,t} k R S)).obj M) h₁).hom ≫
              QV.map (homotopyClass (a.hom.app M))

end

end Specs.DerivedFormalization.Affine.OrdinaryDGTensorComparison
