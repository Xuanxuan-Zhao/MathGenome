import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.StandardHeart
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.KModelMorphisms
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Category.ModuleCat.Ulift
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions

/-!
HA-R11, notes/002/advanced-homological-algebra.tex:2060–2089.
The abelian and universe conventions are those of HA-D03 and HA-D07.
`Ext` is an integer-indexed group of actual morphisms in the unbounded derived
category. No enough-injectives or enough-projectives assumption is made.
The two resolution formulas quantify over a supplied quasi-isomorphism and
only the corresponding termwise injectivity/projectivity and one bound.
The Hom complex has differential d(u) = d_target u - (-1)^j u d_source.
For a stalk in the target the differential is (-1)^(j+1) precomposition.
-/

set_option linter.checkUnivs false
universe w v u z v' z' l
open CategoryTheory CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.StandardHeart
open CochainComplex HomComplex

namespace Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

section
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

abbrev Ext (X Y : A) (n : ℤ) := (stalk A).obj X ⟶ ((stalk A).obj Y)⟦n⟧

noncomputable def extMap {X X' Y Y' : A} (a : X' ⟶ X) (b : Y ⟶ Y')
    (n : ℤ) (x : Ext X Y n) : Ext X' Y' n :=
  (stalk A).map a ≫ x ≫ (CategoryTheory.shiftFunctor _ n).map ((stalk A).map b)

noncomputable def zeroHom {X Y : A} (f : X ⟶ Y) : Ext X Y 0 :=
  (stalk A).map f ≫ (shiftFunctorZero _ ℤ).inv.app _

/-- The canonical map on cohomology classes before choosing either model. -/
noncomputable def classToDerived (K L : CochainComplex A ℤ) (n : ℤ) :
    CohomologyClass K L n →+ (_root_.DerivedCategory.Q.obj K ⟶
      (_root_.DerivedCategory.Q.obj L)⟦n⟧) where
  toFun x := (_root_.DerivedCategory.quotientCompQhIso A).inv.app K ≫
    _root_.DerivedCategory.Qh.map (CohomologyClass.toHom x) ≫
    (_root_.DerivedCategory.quotientCompQhIso A).hom.app (L⟦n⟧) ≫
    (_root_.DerivedCategory.Q.commShiftIso n).hom.app L
  map_zero' := by simp
  map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp]

noncomputable def injectiveClassMap (X Y : A) (I : CochainComplex A ℤ)
    (ι : (CochainComplex.singleFunctor A 0).obj Y ⟶ I) (hι : QuasiIso ι) (n : ℤ)
    (x : CohomologyClass ((CochainComplex.singleFunctor A 0).obj X) I n) : Ext X Y n :=
  letI := hι
  classToDerived _ _ n x ≫
    (CategoryTheory.shiftFunctor _ n).map (inv (_root_.DerivedCategory.Q.map ι))

noncomputable def projectiveClassMap (X Y : A) (P : CochainComplex A ℤ)
    (π : P ⟶ (CochainComplex.singleFunctor A 0).obj X) (hπ : QuasiIso π) (n : ℤ)
    (x : CohomologyClass P ((CochainComplex.singleFunctor A 0).obj Y) n) : Ext X Y n :=
  letI := hπ
  inv (_root_.DerivedCategory.Q.map π) ≫ classToDerived _ _ n x

end

def extType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], A → A → ℤ → Type w
noncomputable def extValue : extType := fun _ _ _ _ => Ext

def zeroType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X Y : A),
  ∃ e : (X ⟶ Y) ≃+ Ext X Y 0, ∀ f, e f = zeroHom f

def zeroNaturalType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X X' Y Y' : A)
  (a : X' ⟶ X) (b : Y ⟶ Y') (f : X ⟶ Y),
  zeroHom (a ≫ f ≫ b) = extMap a b 0 (zeroHom f)

def negativeType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X Y : A) (n : ℤ), n < 0 → ∀ x : Ext X Y n, x = 0

/-- Cohomology of the usual cochain Hom complex, without a resolution assumption. -/
def homologyClassType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (K L : CochainComplex A ℤ) (n : ℤ),
  (HomComplex K L).homology n ≃+ CohomologyClass K L n
noncomputable def homologyClassValue : homologyClassType :=
  fun _ _ _ K L n => HomComplex.homologyAddEquiv K L n

/-- The stalk-source Hom complex really has the ordinary Hom coordinates. -/
def injectiveCoordinatesType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (X : A) (I : CochainComplex A ℤ) (n : ℤ),
  Cochain ((CochainComplex.singleFunctor A 0).obj X) I n ≃+ (X ⟶ I.X n)
noncomputable def injectiveCoordinatesValue : injectiveCoordinatesType :=
  fun _ _ _ _ _ n => Cochain.fromSingleEquiv (zero_add n)

/-- The stalk-target Hom complex has the reversed resolution coordinates. -/
def projectiveCoordinatesType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (Y : A) (P : CochainComplex A ℤ) (n : ℤ),
  Cochain P ((CochainComplex.singleFunctor A 0).obj Y) n ≃+ (P.X (-n) ⟶ Y)
noncomputable def projectiveCoordinatesValue : projectiveCoordinatesType :=
  fun _ _ _ _ _ n => Cochain.toSingleEquiv (neg_add_cancel n)

/-- Full injective comparison, with the canonical formula on every cocycle. -/
def injectiveType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X Y : A) (I : CochainComplex A ℤ)
  (ι : (CochainComplex.singleFunctor A 0).obj Y ⟶ I),
  ∀ hι : QuasiIso ι, (∃ b : ℤ, ∀ i < b, IsZero (I.X i)) →
  (∀ i : ℤ, Injective (I.X i)) → ∀ n : ℤ,
  ∃ e : (HomComplex ((CochainComplex.singleFunctor A 0).obj X) I).homology n ≃+ Ext X Y n,
    ∀ x : CohomologyClass ((CochainComplex.singleFunctor A 0).obj X) I n,
      e ((HomComplex.homologyAddEquiv _ _ n).symm x) = injectiveClassMap X Y I ι hι n x

/-- Full projective comparison with no injectivity hypothesis on the target. -/
def projectiveType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X Y : A) (P : CochainComplex A ℤ)
  (π : P ⟶ (CochainComplex.singleFunctor A 0).obj X),
  ∀ hπ : QuasiIso π, (∃ b : ℤ, ∀ i, b < i → IsZero (P.X i)) →
  (∀ i : ℤ, Projective (P.X i)) → ∀ n : ℤ,
  ∃ e : (HomComplex P ((CochainComplex.singleFunctor A 0).obj Y)).homology n ≃+ Ext X Y n,
    ∀ x : CohomologyClass P ((CochainComplex.singleFunctor A 0).obj Y) n,
      e ((HomComplex.homologyAddEquiv _ _ n).symm x) = projectiveClassMap X Y P π hπ n x

/-- The differential in the injective-resolution Hom coordinates is unsigned. -/
def injectiveDifferentialType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (X : A) (I : CochainComplex A ℤ) (n : ℤ) (f : X ⟶ I.X n),
  δ n (n+1) (Cochain.fromSingleMk f (zero_add n)) =
    Cochain.fromSingleMk (f ≫ I.d n (n+1)) (zero_add (n+1))

/-- For projective cochain coordinates the differential is signed precomposition. -/
def projectiveDifferentialType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (Y : A) (P : CochainComplex A ℤ) (n : ℤ) (f : P.X (-n) ⟶ Y),
  δ n (n+1) (Cochain.toSingleMk f (neg_add_cancel n)) =
    (n+1).negOnePow • Cochain.toSingleMk (P.d (-(n+1)) (-n) ≫ f)
      (neg_add_cancel (n+1))

/-- Naturality on all cocycle representatives, for any lift of a coefficient map.
The equivalences above and surjectivity of cocycles onto cohomology make this
precisely both-variable naturality on cohomology. -/
def injectiveNaturalType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X X' Y Y' : A) (I J : CochainComplex A ℤ)
  (ι : (CochainComplex.singleFunctor A 0).obj Y ⟶ I)
  (ι' : (CochainComplex.singleFunctor A 0).obj Y' ⟶ J)
  (hι : QuasiIso ι) (hι' : QuasiIso ι')
  (a : X' ⟶ X) (b : Y ⟶ Y') (g : I ⟶ J),
  Nonempty (Homotopy (ι ≫ g) ((CochainComplex.singleFunctor A 0).map b ≫ ι')) →
  ∀ (n : ℤ) (z : Cocycle ((CochainComplex.singleFunctor A 0).obj X) I n),
    injectiveClassMap X' Y' J ι' hι' n
      (CohomologyClass.mk ((z.precomp ((CochainComplex.singleFunctor A 0).map a)).postcomp g)) =
    extMap a b n (injectiveClassMap X Y I ι hι n (CohomologyClass.mk z))

def projectiveNaturalType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X X' Y Y' : A) (P P' : CochainComplex A ℤ)
  (π : P ⟶ (CochainComplex.singleFunctor A 0).obj X)
  (π' : P' ⟶ (CochainComplex.singleFunctor A 0).obj X')
  (hπ : QuasiIso π) (hπ' : QuasiIso π')
  (a : X' ⟶ X) (b : Y ⟶ Y') (g : P' ⟶ P),
  Nonempty (Homotopy (g ≫ π) (π' ≫ (CochainComplex.singleFunctor A 0).map a)) →
  ∀ (n : ℤ) (z : Cocycle P ((CochainComplex.singleFunctor A 0).obj Y) n),
    projectiveClassMap X' Y' P' π' hπ' n
      (CohomologyClass.mk ((z.precomp g).postcomp ((CochainComplex.singleFunctor A 0).map b))) =
    extMap a b n (projectiveClassMap X Y P π hπ n (CohomologyClass.mk z))

section Modules
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

/-- The comparison concerns P103's actual quotient model, simultaneously for
all ordinary projective resolutions. Naturality for every augmented lift
includes independence of the resolution and the lift. The degree-zero clause
fixes the comparison on the augmentation. The ring is arbitrary, possibly
noncommutative, and no finiteness assumptions are imposed. -/
structure ModuleComparison (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] where
  equiv : ∀ (X Y : ModuleCat.{max u v} R) (P : LeftResolution R X),
    P.IsProjective → ∀ n : ℕ, ExtWith P Y n ≃+ Ext X Y (n : ℤ)
  natural : ∀ (X X' Y Y' : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' ⟶ X) (b : Y ⟶ Y') (g : P'.complex ⟶ P.complex),
    ChainLift P' P a.hom g → ∀ (n : ℕ) (x : ExtWith P Y n),
    equiv X' Y' P' hP' n
      (homologyMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) n x) =
    extMap a b (n : ℤ) (equiv X Y P hP n x)
  zero : ∀ (X Y : ModuleCat.{max u v} R) (P : LeftResolution R X)
    (hP : P.IsProjective) (z : cycles (homComplex P.complex Y) 0) (f : X ⟶ Y),
    f.hom.comp P.ε = z.val →
    equiv X Y P hP 0 (homologyClass _ 0 z) = zeroHom f

/-- Comparison with the actual P103 quotient model of module Ext. -/
def moduleType : Prop := ∀ (R : Type u) [Ring R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} R)],
  Nonempty (ModuleComparison.{w,v,u} R)

/-- Unlike the signed cochain-Hom complex above, P103 uses unsigned
precomposition on its natural-number-indexed resolution Hom complex. -/
def moduleDifferentialType : Prop := ∀ (R : Type u) [Ring R]
  (C : ChainComplex (ModuleCat.{v} R) ℕ) (Y : ModuleCat.{z} R) (n : ℕ)
  (f : C.X n →ₗ[R] Y),
  ((homComplex C Y).d n (n+1)).hom f = f.comp (C.d (n+1) n).hom

/-- The ambient category for the original modules and the terms of the original
projective resolution. No lift of the ring or change of the module action occurs. -/
abbrev firstLift.{U,V,Z,L} (R : Type U) [Ring R] :
    ModuleCat.{V} R ⥤ ModuleCat.{max U V Z L} R :=
  ModuleCat.uliftFunctor.{max U Z L,V} R

abbrev secondLift.{U,V,Z,L} (R : Type U) [Ring R] :
    ModuleCat.{Z} R ⥤ ModuleCat.{max U V Z L} R :=
  ModuleCat.uliftFunctor.{max U V L,Z} R

abbrev termLift.{U,V,Z,L} (R : Type U) [Ring R] :
    ModuleCat.{max U V} R ⥤ ModuleCat.{max U V Z L} R :=
  ModuleCat.uliftFunctor.{max Z L,max U V} R

/-- From the original, unsigned P103 cochains to maps of lifted terms.
The opposite sign convention in the cochain Hom model is handled separately. -/
def liftCochain.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ)
    (f : P.complex.X n →ₗ[R] Y) :
    (termLift.{U,V,Z,L} R).obj (P.complex.X n) ⟶ (secondLift.{U,V,Z,L} R).obj Y :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (f.comp ULift.moduleEquiv.toLinearMap))

def liftedCochainsType : Prop := ∀ (R : Type u) [Ring R]
    (X : ModuleCat.{v} R) (P : LeftResolution R X) (Y : ModuleCat.{z} R),
    (∀ n : ℕ, Function.Bijective (liftCochain.{u,v,z,0} R P Y n)) ∧
    ∀ (n : ℕ) (f : P.complex.X n →ₗ[R] Y),
      liftCochain.{u,v,z,0} R P Y (n + 1) (((homComplex P.complex Y).d n (n+1)).hom f) =
        (termLift.{u,v,z,0} R).map (P.complex.d (n+1) n) ≫ liftCochain.{u,v,z,0} R P Y n f

abbrev liftedChain.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) :=
  ((termLift.{U,V,Z,L} R).mapHomologicalComplex (.down ℕ)).obj P.complex

/-- Place resolution degree `n` in cochain degree `-n`, without changing
the differentials of the original lifted resolution. -/
noncomputable abbrev liftedResolution.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) :=
  (liftedChain.{U,V,Z,L} R P).extend (ComplexShape.embeddingUpIntLE 0)

noncomputable abbrev liftedTerm.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) (n : ℕ) :
    (liftedResolution.{U,V,Z,L} R P).X (-(n : ℤ)) ≅
      (termLift.{U,V,Z,L} R).obj (P.complex.X n) :=
  (liftedChain.{U,V,Z,L} R P).extendXIso (ComplexShape.embeddingUpIntLE 0) (by simp)

def liftAugmentation.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) :
    (termLift.{U,V,Z,L} R).obj (P.complex.X 0) ⟶ (firstLift.{U,V,Z,L} R).obj X :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (P.ε.comp ULift.moduleEquiv.toLinearMap))

/-- The actual P103 Ext class, covariant in the independently sized original
coefficient and contravariant in the independently sized original resolved
module. The second model uses the stalks of their carrier lifts. -/
structure IndependentModuleComparison.{U,V,Z,L,W} (R : Type U) [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{max U V Z L} R)] where
  equiv : ∀ (X : ModuleCat.{V} R) (Y : ModuleCat.{Z} R) (P : LeftResolution R X),
    P.IsProjective → ∀ n : ℕ, ExtWith P Y n ≃+
      Ext ((firstLift.{U,V,Z,L} R).obj X) ((secondLift.{U,V,Z,L} R).obj Y) (n : ℤ)
  cocycle_formula : ∀ (X : ModuleCat.{V} R) (P : LeftResolution R X) (hP : P.IsProjective),
    ∃ (π : liftedResolution.{U,V,Z,L} R P ⟶
          (CochainComplex.singleFunctor _ 0).obj ((firstLift.{U,V,Z,L} R).obj X))
      (hπ : QuasiIso π),
      π.f 0 ≫ (HomologicalComplex.singleObjXSelf (c := .up ℤ) 0
        ((firstLift.{U,V,Z,L} R).obj X)).hom =
        (liftedTerm.{U,V,Z,L} R P 0).hom ≫ liftAugmentation.{U,V,Z,L} R P ∧
      ∀ (Y : ModuleCat.{Z} R) (n : ℕ) (x : cycles (homComplex P.complex Y) n),
        ∃ y : Cocycle (liftedResolution.{U,V,Z,L} R P)
            ((CochainComplex.singleFunctor _ 0).obj ((secondLift.{U,V,Z,L} R).obj Y)) (n : ℤ),
          y.val = (-1 : ℤ) ^ (n * (n + 1) / 2) • Cochain.toSingleMk
            ((liftedTerm.{U,V,Z,L} R P n).hom ≫ liftCochain.{U,V,Z,L} R P Y n x.val)
            (neg_add_cancel (n : ℤ)) ∧
          equiv X Y P hP n (homologyClass _ n x) =
            projectiveClassMap _ _ _ π hπ (n : ℤ) (CohomologyClass.mk y)
  natural : ∀ (X X' : ModuleCat.{V} R) (Y Y' : ModuleCat.{Z} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' ⟶ X) (b : Y ⟶ Y') (g : P'.complex ⟶ P.complex),
    ChainLift P' P a.hom g → ∀ (n : ℕ) (x : ExtWith P Y n),
    equiv X' Y' P' hP' n
      (homologyMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) n x) =
    extMap ((firstLift.{U,V,Z,L} R).map a) ((secondLift.{U,V,Z,L} R).map b) (n : ℤ) (equiv X Y P hP n x)
  zero : ∀ (X : ModuleCat.{V} R) (Y : ModuleCat.{Z} R) (P : LeftResolution R X)
    (hP : P.IsProjective) (x : cycles (homComplex P.complex Y) 0) (f : X →ₗ[R] Y),
    f.comp P.ε = x.val →
    equiv X Y P hP 0 (homologyClass _ 0 x) =
      zeroHom (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
        (f.comp ULift.moduleEquiv.toLinearMap)))

def independentModuleType : Prop := ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v z} R)],
    Nonempty (IndependentModuleComparison.{u,v,z,0,w} R)

/-- A map between differently sized original modules in the common ambient
category, expressed on the original elements. -/
def liftLinearMap {R : Type u} [Ring R]
    {A : Type v} {B : Type z} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (a : A →ₗ[R] B) :
    ULift.{v'} A →ₗ[R] ULift.{z'} B :=
  ULift.moduleEquiv.symm.toLinearMap.comp (a.comp ULift.moduleEquiv.toLinearMap)

/-- Naturality of the original P103 quotients for maps between independently
sized carriers, using an augmented comparison of the original resolutions
in one common module category. The representative formula fixes the quotient
map by actual precomposition and postcomposition. -/
def heterogeneousModuleType : Prop := ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v z v' z' l} R)],
  ∃ (C : IndependentModuleComparison.{u,v,z,max v' z' l,w} R)
    (C' : IndependentModuleComparison.{u,v',z',max v z l,w} R),
    ∀ (X : ModuleCat.{v} R) (X' : ModuleCat.{v'} R)
      (Y : ModuleCat.{z} R) (Y' : ModuleCat.{z'} R)
      (P : LeftResolution R X) (P' : LeftResolution R X')
      (hP : P.IsProjective) (hP' : P'.IsProjective)
      (a : X' →ₗ[R] X) (b : Y →ₗ[R] Y'),
      let a' : (firstLift.{u,v',z',max v z l} R).obj X' ⟶
          (firstLift.{u,v,z,max v' z' l} R).obj X := ModuleCat.ofHom (liftLinearMap a)
      let b' : (secondLift.{u,v,z,max v' z' l} R).obj Y ⟶
          (secondLift.{u,v',z',max v z l} R).obj Y' := ModuleCat.ofHom (liftLinearMap b)
      let aug := liftAugmentation.{u,v,z,max v' z' l} R P
      let aug' := liftAugmentation.{u,v',z',max v z l} R P'
      (∃ g : liftedChain.{u,v',z',max v z l} R P' ⟶ liftedChain.{u,v,z,max v' z' l} R P,
        g.f 0 ≫ aug = aug' ≫ a') ∧
      ∀ (g : liftedChain.{u,v',z',max v z l} R P' ⟶ liftedChain.{u,v,z,max v' z' l} R P),
      g.f 0 ≫ aug = aug' ≫ a' → ∀ n : ℕ,
      ∃ e : ExtWith P Y n →+ ExtWith P' Y' n,
        (∀ x : cycles (homComplex P.complex Y) n,
          ∃ y : cycles (homComplex P'.complex Y') n,
            (∀ s : P'.complex.X n,
              (show P'.complex.X n →ₗ[R] Y' from y.val) s =
                b ((show P.complex.X n →ₗ[R] Y from x.val) ((g.f n).hom (ULift.up s)).down)) ∧
            e (homologyClass _ n x) = homologyClass _ n y) ∧
        (∀ x : ExtWith P Y n, C'.equiv X' Y' P' hP' n (e x) =
          extMap a' b' (n : ℤ) (C.equiv X Y P hP n x))

end Modules

end Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
