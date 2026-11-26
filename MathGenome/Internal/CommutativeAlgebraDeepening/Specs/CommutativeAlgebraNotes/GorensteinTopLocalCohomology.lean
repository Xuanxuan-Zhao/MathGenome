import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MinimalInjectiveResolutionSocles
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open _root_.CommutativeAlgebraNotes.MinimalInjectiveResolutionSoclesSpecs
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs

namespace Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology

universe u w

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Apply maximal-ideal power torsion to the minimal resolution, extended by
zero to negative degrees. -/
abbrev torsionComplex (J : Resolution (ModuleCat.of R R)) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((IdealTorsion.idealTorsionFunctor (maximalIdeal R)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj J.toInjectiveResolution.cochainComplex

/-- The total right derived functor of maximal-ideal torsion evaluated on the
ring in degree zero, viewed in the derived category. -/
abbrev derivedTorsionOfRing (R : Type u) [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : DerivedCategory (ModuleCat.{u} R) :=
  ((IdealTorsion.idealTorsionFunctor (maximalIdeal R)).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).obj

/-- All terms away from the dimension are zero, and the term in the
dimension is the chosen residue-field hull. -/
def torsionTermProfileType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (_hG : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (_hd : ringKrullDim R = (d : WithBot ℕ∞))
    (J : Resolution (ModuleCat.of R R)) (E : residueFieldEnvelopeValue R),
    (∀ i : ℤ, i ≠ (d : ℤ) → IsZero ((torsionComplex J).X i)) ∧
      Nonempty ((torsionComplex J).X (d : ℤ) ≅ ModuleCat.of R E.carrier)

/-- The complex comparison extends any prescribed identification of the
degree-d term. Changing that identification acts by the corresponding
automorphism of the stalk in degree d. -/
def torsionComplexComparisonType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (_hG : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (_hd : ringKrullDim R = (d : WithBot ℕ∞))
    (J : Resolution (ModuleCat.of R R)) (E : residueFieldEnvelopeValue R),
    let A := ModuleCat.of R E.carrier
    let stalk := CochainComplex.singleFunctor (ModuleCat.{u} R) (d : ℤ)
    ∃ compare : (((torsionComplex J).X (d : ℤ)) ≅ A) → (torsionComplex J ≅ stalk.obj A),
      (∀ e, HomologicalComplex.Hom.isoApp (compare e) (d : ℤ) ≪≫
        HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (d : ℤ) A = e) ∧
      ∀ e f, compare f = compare e ≪≫ stalk.mapIso (e.symm ≪≫ f)

/-- The image of the torsion complex of any chosen minimal resolution
computes the actual total right derived functor on the ring. -/
def torsionComputesDerivedType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (J : Resolution (ModuleCat.of R R)),
    Nonempty (derivedTorsionOfRing R ≅ DerivedCategory.Q.obj (torsionComplex J))

/-- With the resolution comparison fixed, changing the identification in
degree d postcomposes the derived comparison by the shifted hull automorphism. -/
def derivedComparisonChoiceType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (_hG : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (_hd : ringKrullDim R = (d : WithBot ℕ∞))
    (J : Resolution (ModuleCat.of R R)) (E : residueFieldEnvelopeValue R)
    (compute : derivedTorsionOfRing R ≅ DerivedCategory.Q.obj (torsionComplex J)),
    let C := ModuleCat.{u} R
    let A := ModuleCat.of R E.carrier
    let stalk := CochainComplex.singleFunctor C (d : ℤ)
    let shiftedStalk := DerivedCategory.singleFunctor C 0 ⋙
      shiftFunctor (DerivedCategory C) (-(d : ℤ))
    let shiftIso := (DerivedCategory.singleFunctors C).shiftIso
      (-(d : ℤ)) (d : ℤ) 0 (neg_add_cancel _)
    ∃ chainCompare : ((torsionComplex J).X (d : ℤ) ≅ A) → (torsionComplex J ≅ stalk.obj A),
      (∀ e, HomologicalComplex.Hom.isoApp (chainCompare e) (d : ℤ) ≪≫
        HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (d : ℤ) A = e) ∧
      let compare := fun e => compute ≪≫ DerivedCategory.Q.mapIso (chainCompare e) ≪≫
        (shiftIso.app A).symm
      ∀ e f, compare f = compare e ≪≫ shiftedStalk.mapIso (e.symm ≪≫ f)

/-- For a Noetherian Gorenstein local ring of dimension d, the right derived
maximal-ideal torsion of the ring is the residue-field hull shifted by -d. -/
def gorensteinTopLocalCohomologyType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (_hG : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (_hd : ringKrullDim R = (d : WithBot ℕ∞)) (E : residueFieldEnvelopeValue R),
    Nonempty (derivedTorsionOfRing R ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R E.carrier))⟦-(d : ℤ)⟧)

end Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
