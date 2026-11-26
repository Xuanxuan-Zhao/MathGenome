import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AffineTildeAcyclicity
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.InjectiveCechComparison
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicTermComparison
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement

universe u w

variable (R : CommRingCat.{u})

/-- The open complement of the closed set defined by the ideal. -/
def complement (I : Ideal R) : (Spec R).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- Sections, with scalars restricted along the canonical base-ring map. -/
def sections (U : (Spec R).Opens) : (Spec R).Modules ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)

instance (U : (Spec R).Opens) : (sections R U).Additive where
  map_add := by intros; rfl

/-- Restrict sections along an inclusion of opens. -/
def restrict {U V : (Spec R).Opens} (h : U ≤ V) : sections R V ⟶ sections R U where
  app F := (modulesSpecToSheaf.obj F).presheaf.map (homOfLE h).op
  naturality _F _G f := ((modulesSpecToSheaf.map f).1.naturality (homOfLE h).op).symm

/-- The map from the coefficient module into sections of its associated sheaf. -/
def toSections (U : (Spec R).Opens) : 𝟭 (ModuleCat.{u} R) ⟶ tilde.functor R ⋙ sections R U where
  app M := tilde.toOpen M U
  naturality _M _N f := (tilde.toOpen_map_app f U).symm

/-- A generating list defines the distinguished cover of the open complement. -/
def DistinguishedCover : Prop :=
  ∀ (R : CommRingCat.{u}) (I : Ideal R) (rs : List R),
    Ideal.span {r | r ∈ rs} = I →
    complement R I = ⨆ i : Fin rs.length, PrimeSpectrum.basicOpen (rs.get i)

/-- The torsion inclusion followed by the map to sections of the complement. -/
def TorsionKernel : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R) (x : M),
    tilde.toOpen M (complement R I) x = 0 ↔ x ∈ IdealTorsion.idealTorsion I M

/-- The actual sections sequence is short exact on injective coefficient modules. -/
def InjectiveSectionsExact : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) (Q : ModuleCat.{u} R)
    [Injective Q], ∃ w : (IdealTorsion.idealTorsionInclusion I).app Q ≫
      (toSections R (complement R I)).app Q = 0,
      (ShortComplex.mk _ _ w).ShortExact


open HomologicalComplex CategoryTheory.Functor CategoryTheory.Pretriangulated
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency false
open AugmentedCechComplex (coefficients tensorFunctor)
open InjectiveCechComparison (singleZero projection)

local notation "upZ" => ComplexShape.up ℤ

abbrev Cpx := CochainComplex (ModuleCat.{u} R) ℤ

open _root_.AdvancedHomologicalAlgebra.AcyclicTermComparison (brutalCut brutalCutIncl)
open private cutIn cutOut cutOut_cutIn cutIn_cutOut from
  MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicTermComparison

private def positiveTailMap {K L : Cpx R} (f : K ⟶ L) :
    brutalCut K (1 ≤ ·) ⟶ brutalCut L (1 ≤ ·) where
  f i := cutIn K (1 ≤ ·) i ≫ f.f i ≫ cutOut L (1 ≤ ·) i
  comm' i j _ := by
    dsimp [brutalCut]
    simp only [Category.assoc]
    rw [← Category.assoc (cutOut L _ i), cutOut_cutIn,
      ← Category.assoc (cutOut K _ j), cutOut_cutIn]
    by_cases hi : 1 ≤ i <;> by_cases hj : 1 ≤ j
    · simp [hi, hj, f.comm_assoc]
    · simp [hi, hj, cutOut]
    · simp [hi, hj, cutIn]
    · simp [hi, hj]

/-- Remove all terms in degrees less than one. -/
def positiveTail : Cpx R ⥤ Cpx R where
  obj K := brutalCut K (1 ≤ ·)
  map f := positiveTailMap R f
  map_id K := by
    apply HomologicalComplex.hom_ext
    intro i
    simp [positiveTailMap, cutIn_cutOut]
    rfl
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [positiveTailMap, HomologicalComplex.comp_f, Category.assoc]
    rw [← Category.assoc (cutOut _ _ i), cutOut_cutIn]
    by_cases hi : 1 ≤ i
    · simp [hi]
    · simp [hi, cutIn]

/-- The inclusion of the positive tail into the original complex. -/
def positiveTailInclusion : positiveTail R ⟶ 𝟭 (Cpx R) where
  app K := brutalCutIncl K 1
  naturality K L f := by
    apply HomologicalComplex.hom_ext
    intro i
    change (cutIn K (1 ≤ ·) i ≫ f.f i ≫ cutOut L (1 ≤ ·) i) ≫ cutIn L (1 ≤ ·) i =
      cutIn K (1 ≤ ·) i ≫ f.f i
    simp only [Category.assoc, cutOut_cutIn]
    by_cases hi : 1 ≤ i
    · simp [hi]
    · simp [cutIn, hi]

/-- The unaugmented ordered Čech cochain complex, using the shifted sign
convention. Its degree n term is the degree n+1 term of the augmented complex
for n ≥ 0. -/
def unaugmented (rs : List R) : ModuleCat.{u} R ⥤ Cpx R :=
  (singleZero R ⋙ tensorFunctor R rs) ⋙ positiveTail R ⋙
    shiftFunctor (Cpx R) (1 : ℤ)

/-- Sections of the associated sheaf, applied term by term. -/
abbrev sectionComplex (U : (Spec R).Opens) : Cpx R ⥤ Cpx R :=
  (tilde.functor R ⋙ sections R U).mapHomologicalComplex upZ

/-- Restriction of the associated sheaf's sections, applied term by term. -/
def restrictComplex {U V : (Spec R).Opens} (h : U ≤ V) :
    sectionComplex R V ⟶ sectionComplex R U :=
  (whiskerLeft (tilde.functor R) (restrict R h)).mapHomologicalComplex upZ

/-- The augmented and unaugmented complexes fit into the normalized Čech
triangle. Its first map is the projection onto the degree-zero term. -/
def CechTriangle : Prop :=
  ∀ (R : CommRingCat.{u}) [HasDerivedCategory.{w} (ModuleCat.{u} R)] (rs : List R),
    ∃ π : singleZero R ⋙ tensorFunctor R rs ⟶ singleZero R,
      (∀ M, π.app M = projection rs ((singleZero R).obj M)) ∧
      ∃ (e : singleZero R ⋙ DerivedCategory.Q ⟶
          unaugmented R rs ⋙ DerivedCategory.Q)
        (δ : unaugmented R rs ⋙ DerivedCategory.Q ⟶
          (singleZero R ⋙ tensorFunctor R rs ⋙ DerivedCategory.Q) ⋙
            shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)),
        ∀ M, Triangle.mk (DerivedCategory.Q.map (π.app M)) (e.app M) (δ.app M) ∈
          distTriang (DerivedCategory (ModuleCat.{u} R))

/-- The Čech triangle agrees with the fibre triangle of actual restriction on
the tilde image of an injective resolution. -/
def FlasqueConeComparison : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (rs : List R), Ideal.span {r | r ∈ rs} = I →
    let U := complement R I
    ∀ (M : ModuleCat.{u} R) (J : Cpx R) (ι : (singleZero R).obj M ⟶ J),
      QuasiIso ι → J.IsStrictlyGE 0 → (∀ q, Injective (J.X q)) →
        Nonempty (DerivedCategory.Q.mapTriangle.obj
          (CochainComplex.mappingCone.triangle (projection rs ((singleZero R).obj M))) ≅
          DerivedCategory.Q.mapTriangle.obj
          (CochainComplex.mappingCocone.triangle
            ((restrictComplex R (le_top : U ≤ ⊤)).app J)))


open AdvancedHomologicalAlgebra.SheafTheory (IsFlasque)

attribute [local instance] HasDerivedCategory.standard

/-- The canonical derived-sections comparison is an isomorphism on any
bounded-below flasque complex. It is the same natural comparison at every
open, so it intertwines the actual restriction maps. -/
def FlasqueComputesSections : Prop :=
  ∀ (R : CommRingCat.{u}) (U : (Spec R).Opens)
    (K : CochainComplex.Plus (Spec R).Modules),
    (∀ q, IsFlasque (Spec R).ringCatSheaf (K.obj.X q)) →
      IsIso ((sections R U).rightDerivedFunctorPlusUnit.app K)


/-- Sheaves placed in degree zero in the category of bounded-below complexes. -/
def sheafStalkPlus : (Spec R).Modules ⥤ CochainComplex.Plus (Spec R).Modules :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor _ 0)
    (fun _ => ⟨0, inferInstance⟩)

/-- The total right derived functor of sections, evaluated on the associated
module sheaf. The output retains its canonical action of the base ring. -/
def derivedSections (U : (Spec R).Opens) :
    ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  ((tilde.functor R ⋙ sheafStalkPlus R) ⋙ DerivedCategory.Plus.Q) ⋙
    (sections R U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

/-- The derived transformation of the actual restriction of sections. -/
def derivedRestriction {U V : (Spec R).Opens} (h : U ≤ V) :
    derivedSections R V ⟶ derivedSections R U :=
  whiskerLeft _ (whiskerRight (restrict R h).rightDerivedFunctorPlus _)

/-- Natural identification of the unaugmented ordered Čech complex with
derived sections on the open complement, compatible with restriction in the
distinguished fibre triangle. -/
def NaturalDerivedComparison : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) (rs : List R),
    Ideal.span {r | r ∈ rs} = I →
    let U := complement R I
    ∃ (eX : singleZero R ⋙ DerivedCategory.Q ≅ derivedSections R ⊤)
      (eU : unaugmented R rs ⋙ DerivedCategory.Q ≅ derivedSections R U)
      (b : singleZero R ⋙ DerivedCategory.Q ⟶ unaugmented R rs ⋙ DerivedCategory.Q)
      (δ : derivedSections R U ⟶
        (singleZero R ⋙ tensorFunctor R rs ⋙ DerivedCategory.Q) ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)),
      eX.hom ≫ derivedRestriction R (le_top : U ≤ ⊤) = b ≫ eU.hom ∧
      ∀ M, Triangle.mk
        (DerivedCategory.Q.map (projection rs ((singleZero R).obj M)) ≫ eX.hom.app M)
        ((derivedRestriction R (le_top : U ≤ ⊤)).app M) (δ.app M) ∈
          distTriang (DerivedCategory (ModuleCat.{u} R))

end Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
