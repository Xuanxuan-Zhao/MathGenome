import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition

/-! HA-G04, source 2661–2703. All spectral sequences start at E₂.
The page coordinates below are (filtration degree, total degree): thus the
RowDiagram differential has bidegree (r,1-r) in the usual (p,q) coordinates.
A presentation by the actual convergent row diagrams includes all pages,
next-page isomorphisms, filtration steps, inclusions and transition maps.
The natural presentation, including its maps, retains the canonical limiting
comparisons and their naturality supplied by the row system. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open HypercohomologyDerivedNaturality CartanEilenbergData
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]

/-- Evaluation of a page of a spectral sequence with its filtered target. -/
def pageEval (r : ℕ) (p n : ℤ) : RowDiagram C ⥤ C where
  obj X := X.page r p n
  map f := f.page r p n

/-- Evaluation of the ambient target object. -/
def targetEval (n : ℤ) : RowDiagram C ⥤ C where
  obj X := X.target n
  map f := f.target n

/-- Evaluation of an actual filtration step. -/
def stepEval (p n : ℤ) : RowDiagram C ⥤ C where
  obj X := X.step p n
  map f := f.step p n

/-- Eventual pages are the graded pieces of the target filtration, with
vanishing late differentials, uniformly in filtration degree for each n. -/
def Converges (X : RowDiagram C) : Prop := ∀ n : ℤ, ∃ N : ℕ,
  ∀ r : ℕ, N ≤ r → ∀ p : ℤ,
    X.differential r p n = 0 ∧ Nonempty (X.page r p n ≅ cokernel (X.down p n))

section
variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- A descended row construction, with its precise complex-level realization.
Its system supplies finite convergence and natural limiting comparisons. -/
structure DerivedRow where
  system : System G
  resolution : ∀ K : CochainComplex.Plus B, ResolutionData K.obj
  complexes : CochainComplex.Plus B ⥤ RowDiagram C
  derived : DerivedCategory.Plus B ⥤ RowDiagram C
  obj_eq : ∀ K, complexes.obj K = diagram G (system.data K (resolution K))
  map_eq : ∀ {K L : CochainComplex.Plus B} (f : K ⟶ L),
    ∃ (a : (resolution K).bicomplex ⟶ (resolution L).bicomplex)
      (ha : CartanEilenbergComparison.IsLift (resolution K) (resolution L) f.hom a),
      HEq (complexes.map f) (diagramMap G system f a ha)
  factors : DerivedCategory.Plus.Q ⋙ derived ≅ complexes

/-- The localization comparison on the particular complex used for a row. -/
def DerivedRow.complexIso (R : DerivedRow G) (K : CochainComplex.Plus B) :
    R.derived.obj (DerivedCategory.Plus.Q.obj K) ≅
      diagram G (R.system.data K (R.resolution K)) :=
  R.factors.app K ≪≫ eqToIso (R.obj_eq K)

abbrev rowSecondValue (p : ℕ) (q : ℤ) : DerivedCategory.Plus B ⥤ C :=
  DerivedCategory.Plus.homologyFunctor B q ⋙ rightValue G p

abbrev rowTargetValue (n : ℤ) : DerivedCategory.Plus B ⥤ C :=
  G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n

/-- The descended identifications agree with the computed page and the
augmented total target at every localized bounded-below cochain complex. -/
structure RowCoordinates (R : DerivedRow G) where
  second : ∀ p : ℕ, ∀ q : ℤ, R.derived ⋙ pageEval 0 p ((p : ℤ) + q) ≅
    rowSecondValue G p q
  second_eq : ∀ (K : CochainComplex.Plus B) (p : ℕ) (q : ℤ),
    (second p q).hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedRow.complexIso G R K).hom.page 0 p ((p : ℤ) + q) ≫
      ((R.system.data K (R.resolution K)).secondIso p q).hom ≫
      (rightValue G p).map ((DerivedCategory.homologyFunctorFactors B q).inv.app K.obj)
  target : ∀ n : ℤ, R.derived ⋙ targetEval n ≅ rowTargetValue G n
  target_eq : ∀ (K : CochainComplex.Plus B) (n : ℤ),
    (target n).hom.app (DerivedCategory.Plus.Q.obj K) = (DerivedRow.complexIso G R K).hom.target n

/-- The sequence is pulled back along the canonical total RF. -/
abbrev sequence (R : DerivedRow G) : DerivedCategory.Plus A ⥤ RowDiagram C :=
  F.rightDerivedFunctorPlus ⋙ R.derived

/-- The desired E₂, including its action on every derived morphism. -/
abbrev secondValue (p : ℕ) (q : ℤ) : DerivedCategory.Plus A ⥤ C :=
  F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q ⋙ rightValue G p

/-- Hⁿ of the iterated derived functor. -/
abbrev iteratedValue (n : ℤ) : DerivedCategory.Plus A ⥤ C :=
  (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙
    DerivedCategory.Plus.homologyFunctor C n

/-- Hⁿ R(GF). -/
abbrev compositeValue (n : ℤ) : DerivedCategory.Plus A ⥤ C :=
  (F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n

/-- Full natural spectral sequence and its finite filtered target. A row
presentation supplies convergence to the associated graded, not merely an
isomorphism of the unfiltered targets. The final equality requires transport
along exactly the canonical HA-R12 comparison. -/
structure Package where
  row : DerivedRow G
  secondIso : ∀ (p : ℕ) (q : ℤ), sequence F G row ⋙ pageEval 0 (p : ℤ) ((p : ℤ)+q) ≅
    secondValue F G p q
  coordinates : RowCoordinates G row
  second_eq : ∀ (p : ℕ) (q : ℤ), secondIso p q =
    associator _ _ _ ≪≫ isoWhiskerLeft F.rightDerivedFunctorPlus (coordinates.second p q) ≪≫
      (associator _ _ _).symm
  negative : ∀ (X : DerivedCategory.Plus A) (p q : ℤ), p < 0 →
    IsZero (((sequence F G row).obj X).page 0 p (p+q))
  comparison_isIso : ∀ X : DerivedCategory.Plus A,
    IsIso ((Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G).app X)
  iteratedIso : ∀ n, sequence F G row ⋙ targetEval n ≅ iteratedValue F G n
  iterated_eq : ∀ n, iteratedIso n =
    associator _ _ _ ≪≫ isoWhiskerLeft F.rightDerivedFunctorPlus (coordinates.target n) ≪≫
      (associator _ _ _).symm
  targetIso : ∀ n, sequence F G row ⋙ targetEval n ≅ compositeValue F G n
  canonical : ∀ n, letI := comparison_isIso
    letI : IsIso (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G) :=
      NatIso.isIso_of_isIso_app _
    targetIso n = iteratedIso n ≪≫
      isoWhiskerRight (asIso (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G)).symm
        (DerivedCategory.Plus.homologyFunctor C n)
  convergence : ∀ X, Converges ((sequence F G row).obj X)
  down_inclusion : ∀ X p n,
    ((sequence F G row).obj X).down p n ≫ ((sequence F G row).obj X).inclusion p n =
      ((sequence F G row).obj X).inclusion (p+1) n
  inclusion_mono : ∀ X p n, Mono (((sequence F G row).obj X).inclusion p n)
  finite : ∀ X n, ∃ a b : ℤ,
    (∀ p, p ≤ a → IsIso (((sequence F G row).obj X).inclusion p n)) ∧
    (∀ p, b ≤ p → IsZero (((sequence F G row).obj X).step p n))

/-- The filtration on the stated abutment is the actual diagram filtration
transported through the canonical composition isomorphism. -/
def targetFiltration (P : Package F G) (X : DerivedCategory.Plus A) (p n : ℤ) :
    Subobject ((compositeValue F G n).obj X) :=
  imageSubobject ((((sequence F G P.row).obj X).inclusion p n) ≫ (P.targetIso n).hom.app X)
end

namespace Specs
/-- No preservation of injectives by F is assumed. Only A and B need enough
injectives. Left exactness is preservation of finite limits, with the standing
additivity convention of the source. -/
def FullStatement : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G],
    (∀ I : A, Injective I →
      _root_.Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue G (F.obj I)) →
    Nonempty (Package F G)
end Specs
end AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
