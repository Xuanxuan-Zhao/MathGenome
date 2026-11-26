import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedPinnedOuterComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalAdaptedRootCoordinates

open AdjointCocharacters (coordinateHopf)
open CharacterDescent (Character)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open ExceptionalAffineBruhat (ExceptionalNumbering FieldPoints RamifiedReference)
open ExceptionalAffineRootSystems (restrictedRoot)
open ExceptionalInnerIndices (HasInnerIndex IsSplitOfRank e6Black e7Black)
open ExceptionalInnerStandardTorusDescent (IsUnitComparison)
open ExceptionalIwahoriImageComparison (markedGroundPoint)
open ExceptionalMarkedRootDescent (MarkedFibre)
open ExceptionalValuedTorusNormalizer (simplePermutationHom)
open GeometricRadicals (IsMaximalTorus)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)
open QuasiSplitPinnedPairModel (BorelPair IsTransportedBasedAction)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open RelativeRank (relativeRank)
open LinearAlgebraicGroups.Descent.Forms (IsScalarExtensionComparison)

set_option maxHeartbeats 800000
set_option maxRecDepth 1024
set_option backward.isDefEq.respectTransparency false

noncomputable section

private abbrev Gm (F : Type u) [Field F] := specGroup (groupAlgebra F IntegerCharacters)

variable {F : Type u} [Field F]

/-- A minimal rational parabolic and its tori with their comparison to the
actual split marked fibre. -/
structure AdaptedBorel (G : AffineAlgebraicGroup F) {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M (SeparableClosure F)) where
  S : ClosedSubgroup G.val
  T : ClosedSubgroup G.val
  J : ClosedSubgroup G.val
  maximalSplit : IsMaximalSplitTorus S
  maximalTorus : IsMaximalTorus T
  minimalParabolic : IsMinimalParabolic G J
  intoTorus : S.group ⟶ T.group
  intoTorus_eq : intoTorus ≫ T.inclusion = S.inclusion
  intoParabolic : T.group ⟶ J.group
  intoParabolic_eq : intoParabolic ≫ J.inclusion = T.inclusion
  ambient : C.realization.pinned.pair.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val
  torus : (groupBaseChange F (SeparableClosure F)).obj T.group ≅ C.realization.pinned.pair.T.group
  torus_eq : torus.hom ≫ C.realization.pinned.pair.T.inclusion ≫ ambient.hom =
    (groupBaseChange F (SeparableClosure F)).map T.inclusion
  borel : C.realization.pinned.pair.B.group ⟶ (groupBaseChange F (SeparableClosure F)).obj J.group
  borel_eq : borel ≫ (groupBaseChange F (SeparableClosure F)).map J.inclusion =
    C.realization.pinned.pair.B.inclusion ≫ ambient.hom
  multiplicative : Gm (SeparableClosure F) ≅ (groupBaseChange F (SeparableClosure F)).obj (Gm F)
  multiplicative_eq : IsUnitComparison F (SeparableClosure F) multiplicative

variable {G : AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {M : Model D}

/-- Restrict the marked simple character through the actual inclusion of
the scalar-extended split torus. -/
abbrev AdaptedBorel.restrictSimple {C : MarkedFibre M (SeparableClosure F)}
    (A : AdaptedBorel G C) (i : D.base.support) :
    Character ((groupBaseChange F (SeparableClosure F)).obj A.S.group) := by
  let α : Character C.realization.pinned.pair.T.group := (C.realization.simpleRoot i).val.val
  exact (groupBaseChange F (SeparableClosure F)).map A.intoTorus ≫ A.torus.hom ≫ α

/-- The scalar extension of a relative character uses the unit-preserving
comparison of the two multiplicative groups. -/
abbrev AdaptedBorel.extendCharacter {C : MarkedFibre M (SeparableClosure F)}
    (A : AdaptedBorel G C) (χ : Character A.S.group) :
    Character ((groupBaseChange F (SeparableClosure F)).obj A.S.group) :=
  (groupBaseChange F (SeparableClosure F)).map χ ≫ A.multiplicative.inv

/-- The restriction of each numbered simple root is the corresponding
projected coordinate vector in the split character lattice. -/
def HasRootCoordinates {n r : ℕ} {C : MarkedFibre M (SeparableClosure F)}
    (A : AdaptedBorel G C)
    (b : Fin n ≃ D.base.support) (project : (Fin n → ℤ) → (Fin r → ℤ)) : Prop := by
  exact ∃ encode : Multiplicative (Fin r → ℤ) →* Character A.S.group,
    Function.Injective encode ∧
    ∀ (i : Fin n), A.restrictSimple (b i) =
      A.extendCharacter (encode (Multiplicative.ofAdd (project (Pi.single i 1))))

def e6InnerProjection (v : Fin 6 → ℤ) : Fin 2 → ℤ := ![v 1, v 3]

def e7InnerProjection (v : Fin 7 → ℤ) : Fin 4 → ℤ := ![v 0, v 2, v 3, v 5]

section ScalarExtension

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The comparison of split fibres respects the original integral marking
on each test algebra. -/
abbrev RespectsIntegralMarking (C₀ : MarkedFibre M K) (C₁ : MarkedFibre M L)
    (j : C₁.realization.pinned.pair.G.val ≅
      (groupBaseChange K L).obj C₀.realization.pinned.pair.G.val) : Prop :=
  ExceptionalAdaptedPinnedOuterComparison.RespectsIntegralMarking C₀ C₁ j

variable [Algebra F K] [Algebra F L]

/-- The tower comparison preserves the canonical projection to the
original scheme. -/
abbrev IsTowerComparison
    (a : groupBaseChange F K ⋙ groupBaseChange K L ≅ groupBaseChange F L) : Prop :=
  ExceptionalAdaptedPinnedOuterComparison.IsTowerComparison a

/-- The isomorphism of scalar-extended schemes induced by the supplied
coordinate Hopf comparison. -/
abbrev descentComparison (H H' : AffineAlgebraicGroup F)
    (t : ∀ B : HopfAlgebraCategory F,
      specGroup (extendedHopf K B) ≅ (groupBaseChange F K).obj (specGroup B))
    (i : extendedHopf K (coordinateHopf H) ≅ extendedHopf K (coordinateHopf H')) :
    (groupBaseChange F K).obj H.val ≅ (groupBaseChange F K).obj H'.val :=
  ExceptionalAdaptedPinnedOuterComparison.descentComparison H H' t i

end ScalarExtension

/-- Extend the actual adapted marking at the finite inner splitting level
through its normalizer conjugation. -/
def InnerCoordinates (n r : ℕ) (black : Set (Fin n))
    (project : (Fin n → ℤ) → (Fin r → ℤ)) : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {M : Model D}
    (C₀ : MarkedFibre M K) (b : Fin n ≃ D.base.support),
    ExceptionalNumbering D n b →
    ∀ (f : C₀.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj G.val)
      (N : Set (FieldPoints M K)),
    (∀ (g : 𝟙_ (SchemeOver K) ⟶ C₀.realization.pinned.pair.G.val.X),
      markedGroundPoint C₀ g ∈ N → Normalizes C₀.realization.pinned.pair.T.inclusion g) →
    HasInnerIndex b r black C₀ f N →
    ∃ (e : K →ₐ[F] (SeparableClosure F)),
      letI : Algebra K (SeparableClosure F) := e.toRingHom.toAlgebra
      ∃ (C : MarkedFibre M (SeparableClosure F)) (A : AdaptedBorel G C)
        (a : groupBaseChange F K ⋙ groupBaseChange K (SeparableClosure F) ≅ groupBaseChange F (SeparableClosure F))
        (j : C.realization.pinned.pair.G.val ≅
          (groupBaseChange K (SeparableClosure F)).obj C₀.realization.pinned.pair.G.val)
        (g : 𝟙_ (SchemeOver K) ⟶ C₀.realization.pinned.pair.G.val.X),
      IsTowerComparison a ∧ RespectsIntegralMarking C₀ C j ∧ markedGroundPoint C₀ g ∈ N ∧
      (let g' := scalarExtendedRationalPoint (SeparableClosure F) g
       let z : C.realization.pinned.pair.G.val.X ⟶
           ((groupBaseChange K (SeparableClosure F)).obj C₀.realization.pinned.pair.G.val).X :=
         toUnit _ ≫ g'
       (A.ambient.hom ≫ (a.app G.val).inv ≫
          (groupBaseChange K (SeparableClosure F)).map f.inv).hom.hom =
        z⁻¹ * j.hom.hom.hom * z) ∧
      IsSplitOfRank A.S.group r ∧ relativeRank G = r ∧
      (∀ i, i ∈ black ↔ A.restrictSimple (b i) = 1) ∧ HasRootCoordinates A b project

/-- The two inner exceptional indices in zero-based Bourbaki numbering. -/
def InnerStatement : Prop :=
  InnerCoordinates.{u} 6 2 e6Black e6InnerProjection ∧
  InnerCoordinates.{u} 7 4 e7Black e7InnerProjection

/-- The outer chart comes from the specified pinned descent, with the
opposite rational Borel pair on the given group. The splitting extension
may contain the quadratic diagram field and may be ramified. -/
def OuterStatement : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {M : Model D}
    (R : RamifiedReference F K M) (b : Fin 6 ≃ D.base.support),
    ExceptionalNumbering D 6 b →
    (∃ (σ : Gal(K/F)) (i : Fin 6), simplePermutationHom D
      (ExceptionalValuedTorusNormalizer.markedDiagramEquiv R.fibre.realization (R.outer σ))
      (b i) ≠ b i) →
    ∀ f : R.descent.group.val ≅ G.val,
    ∃ (e : K →ₐ[F] (SeparableClosure F)),
      letI : Algebra K (SeparableClosure F) := e.toRingHom.toAlgebra
      ∃ (C : MarkedFibre M (SeparableClosure F)) (A : AdaptedBorel G C) (P : BorelPair G)
        (a : groupBaseChange F K ⋙ groupBaseChange K (SeparableClosure F) ≅ groupBaseChange F (SeparableClosure F))
        (j : C.realization.pinned.pair.G.val ≅
          (groupBaseChange F (SeparableClosure F)).obj R.fibre.realization.pinned.pair.G.val)
        (t : ∀ B : HopfAlgebraCategory F,
          specGroup (extendedHopf K B) ≅ (groupBaseChange F K).obj (specGroup B))
        (fB : R.descent.borel.group ≅ P.positive.group)
        (fT : R.descent.torus.group ≅ P.torus.group),
      IsTowerComparison a ∧ RespectsIntegralMarking R.fibre C j ∧
      IsScalarExtensionComparison t ∧ IsTransportedBasedAction R.descent.data ∧
      A.ambient = j ≪≫ (a.app _).symm ≪≫
        (groupBaseChange K (SeparableClosure F)).mapIso
          (descentComparison _ _ t R.descent.data.groupIso) ≪≫
        a.app R.descent.group.val ≪≫ (groupBaseChange F (SeparableClosure F)).mapIso f ∧
      P.positive = A.J ∧ P.torus = A.T ∧
      fB.hom ≫ P.positive.inclusion = R.descent.borel.inclusion ≫ f.hom ∧
      fT.hom ≫ P.torus.inclusion = R.descent.torus.inclusion ≫ f.hom ∧
      IsSplitOfRank A.S.group 4 ∧ relativeRank G = 4 ∧ HasRootCoordinates A b restrictedRoot

end

end LinearAlgebraicGroups.Specs.ExceptionalAdaptedRootCoordinates
