import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
HA-R09 values and connecting maps, source 2001–2021, with chapter conventions
1767–1775. The universality and long exact delta-functor assertions are allocated
to HA-R09 (UniversalDeltaFunctors). No exactness of F is required for values, computation,
vanishing on models, or connecting maps. Classical indices are natural numbers;
the projective resolution is a cochain complex supported in degrees ≤ 0.
-/
set_option linter.checkUnivs false
set_option linter.unusedVariables false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

namespace Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

section MappedStalk
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- Compare the termwise image of a stalk in the homotopy category with the
stalk of its image in the abelian category. -/
private noncomputable def mappedStalkIso (F : A ⥤ B) [F.Additive] :
    HomotopyCategory.singleFunctor A 0 ⋙ F.mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh ≅ F ⋙ DerivedCategory.singleFunctor B 0 := by
  calc
    _ ≅ CochainComplex.singleFunctor A 0 ⋙
          (HomotopyCategory.quotient A (.up ℤ) ⋙ F.mapHomotopyCategory (.up ℤ)) ⋙
          DerivedCategory.Qh :=
      (associator _ _ _).symm ≪≫ isoWhiskerRight
        (isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso A 0) _ ≪≫
          associator _ _ _) _
    _ ≅ CochainComplex.singleFunctor A 0 ⋙ F.mapHomologicalComplex (.up ℤ) ⋙
          (HomotopyCategory.quotient B (.up ℤ) ⋙ DerivedCategory.Qh) :=
      isoWhiskerLeft _
        (isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫ associator _ _ _)
    _ ≅ (CochainComplex.singleFunctor A 0 ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙
          DerivedCategory.Q :=
      isoWhiskerLeft _ (isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm) ≪≫
        (associator _ _ _).symm
    _ ≅ F ⋙ DerivedCategory.singleFunctor B 0 :=
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0) _ ≪≫
        associator _ _ _ ≪≫ isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQ B 0).symm
end MappedStalk

section Stalks
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

noncomputable def minusSingle : A ⥤ DerivedCategory.Minus A :=
  DerivedCategory.TStructure.t.minus.lift (DerivedCategory.singleFunctor A 0)
    (fun X => ⟨0, inferInstance⟩)

/-- The short exact sequence of stalks, inside D⁺. -/
noncomputable def plusTriangle {S : ShortComplex A} (hS : S.ShortExact) :
    Pretriangulated.Triangle (DerivedCategory.Plus A) :=
  Pretriangulated.Triangle.mk
    ((DerivedCategory.Plus.singleFunctor A 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor A 0).map S.g)
    (DerivedCategory.TStructure.t.plus.homMk (hS.singleδ ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁)))

/-- The same actual derived triangle inside D⁻. -/
noncomputable def minusTriangle {S : ShortComplex A} (hS : S.ShortExact) :
    Pretriangulated.Triangle (DerivedCategory.Minus A) :=
  Pretriangulated.Triangle.mk ((minusSingle A).map S.f) ((minusSingle A).map S.g)
    (DerivedCategory.TStructure.t.minus.homMk (hS.singleδ ≫
      (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).inv.app ((minusSingle A).obj S.X₁)))
end Stalks

section Right
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]

/-- RⁿF = Hⁿ RF(-[0]), including its action on morphisms. -/
noncomputable def rightValue (F : A ⥤ B) [F.Additive] (n : ℕ) : A ⥤ B :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor B (n : ℤ)

/-- The degree-zero comparison `F ⟶ R⁰F` induced by the HA-R06 unit. -/
noncomputable def rightDegreeZeroUnit (F : A ⥤ B) [F.Additive] : F ⟶ rightValue F 0 := by
  let stalk := HomotopyCategory.Plus.singleFunctor A 0
  let sourceStalk : stalk ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.singleFunctor A 0 :=
    ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight A).preimageIso
      (DerivedCategory.singleFunctorIsoCompQh A 0).symm
  let mappedStalk : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ≅ stalk ⋙ plusUValue F :=
    ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight A).preimageIso
      (mappedStalkIso F).symm
  let stalkUnit : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ⟶
      DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus :=
    mappedStalk.hom ≫ whiskerLeft stalk F.rightDerivedFunctorPlusUnith ≫
      (associator _ _ _).inv ≫ whiskerRight sourceStalk.hom _
  exact (isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0)).inv ≫
    whiskerRight stalkUnit (DerivedCategory.Plus.homologyFunctor B 0)

/-- Boundary induced by the third arrow of RF applied to the stalk SES triangle. -/
noncomputable def rightBoundary (F : A ⥤ B) [F.Additive]
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (rightValue F n).obj S.X₃ ⟶ (rightValue F (n + 1)).obj S.X₁ :=
  (DerivedCategory.Plus.homologyFunctor B 0).homologySequenceδ
    (F.rightDerivedFunctorPlus.mapTriangle.obj (plusTriangle A hS))
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)
end Right

section Left
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated]

/-- LₙF = H⁻ⁿ LF(-[0]); R is arbitrary exact left derived data from HA-R07. -/
noncomputable def leftValue (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) (n : ℕ) : A ⥤ B :=
  minusSingle A ⋙ R.functor ⋙ DerivedCategory.Minus.ι ⋙
    DerivedCategory.homologyFunctor B (-(n : ℤ))

/-- The degree-zero comparison `L₀F ⟶ F` induced by the HA-R07 counit. -/
noncomputable def leftDegreeZeroCounit (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) : leftValue F R 0 ⟶ F := by
  let stalk : A ⥤ KMinus A :=
    (minus A).lift (HomotopyCategory.singleFunctor A 0)
      (fun X => (minusStalkValue X).property)
  let sourceStalk : minusSingle A ≅ stalk ⋙ QMinus A :=
    ((FullyFaithful.ofFullyFaithful DerivedCategory.Minus.ι).whiskeringRight A).preimageIso
      (DerivedCategory.singleFunctorIsoCompQh A 0)
  let mappedStalk : stalk ⋙ minusUValue F ⋙ DerivedCategory.Minus.ι ≅
      F ⋙ DerivedCategory.singleFunctor B 0 := mappedStalkIso F
  let derivedCounit : minusSingle A ⋙ R.functor ⟶ stalk ⋙ minusUValue F :=
    whiskerRight sourceStalk.hom _ ≫ (associator _ _ _).hom ≫ whiskerLeft stalk R.counit
  let stalkCounit : minusSingle A ⋙ R.functor ⋙ DerivedCategory.Minus.ι ⟶
      F ⋙ DerivedCategory.singleFunctor B 0 :=
    (associator _ _ _).inv ≫ whiskerRight derivedCounit _ ≫
      (associator _ _ _).hom ≫ mappedStalk.hom
  exact whiskerRight stalkCounit (DerivedCategory.homologyFunctor B 0) ≫
    (isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0)).hom

noncomputable def leftBoundary (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (leftValue F R (n + 1)).obj S.X₃ ⟶ (leftValue F R n).obj S.X₁ := by
  letI := R.commShift
  exact (DerivedCategory.homologyFunctor B 0).homologySequenceδ
    ((R.functor ⋙ DerivedCategory.Minus.ι).mapTriangle.obj (minusTriangle A hS))
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)
end Left

/- The canonical functors and boundaries above are shared definitions in the
independent specification. The implementation targets below assert their
computation, vanishing, degree-zero identifications, and naturality. -/

/-- Every ordinary injective resolution, not only a chosen replacement, computes
all the values. Strict lower bound zero and the quasi-isomorphism express the
usual exact augmented resolution in an arbitrary abelian category. -/
def rightComputationType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive]
    (X : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj X ⟶ I),
    QuasiIso i → (∀ q : ℤ, Injective (I.X q)) → ∀ n : ℕ,
      Nonempty ((rightValue F n).obj X ≅
        ((F.mapHomologicalComplex (.up ℤ)).obj I).homology (n : ℤ))

def leftComputationType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (X : A) (P : CochainComplex A ℤ) [P.IsStrictlyLE 0]
    (p : P ⟶ (CochainComplex.singleFunctor A 0).obj X),
    QuasiIso p → (∀ q : ℤ, Projective (P.X q)) → ∀ n : ℕ,
      Nonempty ((leftValue F R n).obj X ≅
        ((F.mapHomologicalComplex (.up ℤ)).obj P).homology (-(n : ℤ)))

def rightInjectiveVanishingType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (X : A) [Injective X] (n : ℕ),
    IsZero ((rightValue F (n + 1)).obj X)

def leftProjectiveVanishingType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F) (X : A) [Projective X] (n : ℕ),
    IsZero ((leftValue F R (n + 1)).obj X)

/-- Left exactness makes `F ⟶ R⁰F` invertible. -/
def rightZeroType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F],
    IsIso (rightDegreeZeroUnit F)

/-- Right exactness makes `L₀F ⟶ F` invertible. -/
def leftZeroType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F) [PreservesFiniteColimits F],
    IsIso (leftDegreeZeroCounit F R)

def rightConnectingNaturalType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive]
    (S T : ShortComplex A) (hS : S.ShortExact) (hT : T.ShortExact)
    (f : S ⟶ T) (n : ℕ),
    (rightValue F n).map f.τ₃ ≫ rightBoundary F hT n =
      rightBoundary F hS n ≫ (rightValue F (n + 1)).map f.τ₁

def leftConnectingNaturalType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (S T : ShortComplex A) (hS : S.ShortExact) (hT : T.ShortExact)
    (f : S ⟶ T) (n : ℕ),
    (leftValue F R (n + 1)).map f.τ₃ ≫ leftBoundary F R hT n =
      leftBoundary F R hS n ≫ (leftValue F R n).map f.τ₁

end Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
