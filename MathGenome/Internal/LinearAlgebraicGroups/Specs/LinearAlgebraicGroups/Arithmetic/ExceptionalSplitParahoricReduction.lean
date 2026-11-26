import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding

namespace LinearAlgebraicGroups.Specs.ExceptionalSplitParahoricReduction

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj WithZero
open ExceptionalAffineRootSystems (ApartmentRoots)
open ExceptionalAffineBruhat
open ExceptionalAffineBuilding
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model integerAlgebra fibre splitTorus IntegralPoints
  forgetFibrePoint torusPoint cocharacter)
open ExceptionalIwahoriCongruence (integralRing changeRingHom
  localIntegers localIntegersInclusion residueHom)
open ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex residueMap)
open ExceptionalMarkedRootDescent (MarkedFibre)
open ExceptionalIwahoriImageComparison (MarkedCentralCover)
open AdjointRepresentation (GroupPoints)
open GeometricRadicals (IsReductive IsSplitTorus IsMaximalTorus)
open GeometricBorelConjugacy (IsKBorel)

attribute [local instance] integerAlgebra

noncomputable section

section FaceResidue

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)

local notation "A" => ApartmentRoots.split E.datum ℚ
local notation "P(" T ")" => parahoric Y.ad T

/-- Chambers of the given adjoint building whose closure contains the marked point. -/
def IncidentChambers (z : B.ad.realization.Point) : Set (FieldPoints M' K ⧸ Y.ad.I) :=
  {q | ∃ (g : Y.ad.G₀) (t : Weights (ApartmentRoots.SimpleWall A p')),
    q = QuotientGroup.mk (g : FieldPoints M' K) ∧ B.ad.realization.place g t = z}

/-- Reduction of the actual parahoric after scaling in the integral split model. -/
structure FaceReduction
    (t : Weights (ApartmentRoots.SimpleWall A p')) (x : ℚ ⊗[ℤ] E.Y)
    (d : ℕ) (y : E.Y) (π : Kˣ)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    (ξ : Lˣ) where
  parameter : (ξ : L) ^ d = algebraMap K L (π : K)
  same_residue : Function.Bijective (residueMap K L)
  integral : P(cotype t) →* IntegralPoints M'.group (localIntegers L)
  scale (g : P(cotype t)) :
    let R := integralRing L
    let s := torusPoint E R (cocharacter E y R ξ) ≫ M'.torus.hom.hom
    changeRingHom M'.group (localIntegersInclusion L) (integral g) =
      s * scalarPoints M' (algebraMap K L) (g : FieldPoints M' K) * s⁻¹
  muGroup : GroupScheme (residue L)
  unitPoints : (groupPointsFunctor (residue L)).obj muGroup ≅
    DiagonalizableGroups.rootsOfUnityPoints (residue L) d
  μImage : muGroup ⟶ (fibre (residue L)).obj M'.group
  μImage_cocharacter (R : TestAlgebra (residue L)) (r : GroupPoints muGroup R) :
    let s : rootsOfUnity d R := unitPoints.hom.app R r
    forgetFibrePoint M'.group R (r ≫ μImage.hom.hom) =
      torusPoint E (integralRing R) (cocharacter E y (integralRing R) s.val) ≫ M'.torus.hom.hom
  centralizer : ClosedSubgroup ((fibre (residue L)).obj M'.group)
  centralizes : RepresentsSubgroup centralizer (fun _ g => Centralizes μImage g)
  centralizer_smooth : Smooth centralizer.group.X.hom
  identityComponent : ClosedSubgroup centralizer.group
  component_open : IsOpenImmersion identityComponent.inclusion.hom.hom.left
  component_eq : Set.range identityComponent.inclusion.hom.hom.left =
    connectedComponent (η[centralizer.group.X].left
      (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of (residue L))))))
  group_is_affine : IsAffine identityComponent.group.X.left
  group_lft : LocallyOfFiniteType identityComponent.group.X.hom
  group_qc : QuasiCompact identityComponent.group.X.hom
  reductive : IsReductive ⟨identityComponent.group, group_is_affine, group_lft, group_qc⟩
  torus : ClosedSubgroup identityComponent.group
  torusComparison : (fibre (residue L)).obj (splitTorus E) ≅ torus.group
  torus_marked :
    torusComparison.hom ≫ torus.inclusion ≫ identityComponent.inclusion ≫ centralizer.inclusion =
      (fibre (residue L)).map M'.torus
  torus_split : IsSplitTorus torus.group
  torus_maximal : ∃ h : IsClosedImmersion
      ((groupBaseChange (residue L) (AlgebraicClosure (residue L))).map torus.inclusion).hom.hom.left,
    IsMaximalTorus (GeometricRadicals.baseChangedSubgroup (AlgebraicClosure (residue L)) torus h)
  ambientMarking : MarkedFibre M' (residue L)
  root_characters :
    CharacterPairing.absoluteRoots torus =
      (fun a : E.I => Pinning.transportCharacter (ambientMarking.torusIso.symm ≪≫ torusComparison)
        (ambientMarking.realization.datumIso.val.indexEquiv a).val) ''
        {a | ∃ j : ℤ, (A).root a x = j}
  roots (a : E.I) :
    (∃ r : (fibre (residue L)).obj M'.line.group ⟶ identityComponent.group,
      r ≫ identityComponent.inclusion ≫ centralizer.inclusion =
        (fibre (residue L)).map (M'.root a)) ↔ ∃ j : ℤ, (A).root a x = j
  borel : ClosedSubgroup identityComponent.group
  borel_is_borel : IsKBorel borel
  borel_torus : SchemeDerivedGroup.IsSubgroupOf torus borel
  borel_roots (a : E.I) :
    (∃ r : (fibre (residue L)).obj M'.line.group ⟶ borel.group,
      r ≫ borel.inclusion ≫ identityComponent.inclusion ≫ centralizer.inclusion =
        (fibre (residue L)).map (M'.root a)) ↔
      ∃ j : ℤ, (A).root a x = j ∧ (A).positive p' (a, -j)
  reduction : P(cotype t) →*
    GroupPoints identityComponent.group (CommAlgCat.of (residue L) (residue L))
  reduction_eq (g : P(cotype t)) :
    forgetFibrePoint M'.group (CommAlgCat.of (residue L) (residue L))
      (reduction g ≫ identityComponent.inclusion.hom.hom ≫ centralizer.inclusion.hom.hom) =
        changeRingHom M'.group (residueHom (localIntegers L)) (integral g)
  reduction_surjective : Function.Surjective reduction
  preimage_borel (g : P(cotype t)) :
    (∃ b : GroupPoints borel.group (CommAlgCat.of (residue L) (residue L)),
      b ≫ borel.inclusion.hom.hom = reduction g) ↔ (g : FieldPoints M' K) ∈ Y.ad.I
  iwahori_image (b : GroupPoints borel.group (CommAlgCat.of (residue L) (residue L))) :
    ∃ g : P(cotype t), (g : FieldPoints M' K) ∈ Y.ad.I ∧
      reduction g = b ≫ borel.inclusion.hom.hom
  flags : QuotientEmbedding.Presentation borel
  flag_surjective : Function.Surjective (fun g : GroupPoints identityComponent.group
      (CommAlgCat.of (residue L) (residue L)) => g ≫ flags.projection)
  flag_fibres (a b : GroupPoints identityComponent.group
      (CommAlgCat.of (residue L) (residue L))) :
    a ≫ flags.projection = b ≫ flags.projection ↔
      ∃ r : GroupPoints borel.group (CommAlgCat.of (residue L) (residue L)),
        r ≫ borel.inclusion.hom.hom = a⁻¹ * b
  incident : IncidentChambers B (B.ad.realization.place 1 t) ≃
    Points flags.scheme (CommAlgCat.of (residue L) (residue L))
  incident_eq (g : P(cotype t)) (q : IncidentChambers B (B.ad.realization.place 1 t))
      (hq : q.val = QuotientGroup.mk (g : FieldPoints M' K)) :
    incident q = reduction g ≫ flags.projection

end FaceResidue

/-- Scaled residue comparison at the point in the relative interior of the
standard face, with the weights and face subgroup from the marked building. -/
def SplitFaceResidue : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
    (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))
    (x : ℚ ⊗[ℤ] E.Y),
    ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t →
    ∀ (d : ℕ) (y : E.Y), 0 < d → (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y →
    ∀ (π : Kˣ), normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ) →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : ValuativeExtension K L) (ξ : Lˣ),
      Algebra.adjoin K ({(ξ : L)} : Set L) = ⊤ ∧ Module.finrank K L = d ∧
      ramificationIndex K L = (d : ℤ) ∧ normalizedValuation L (ξ : L) = WithZero.exp (-1 : ℤ) ∧
      Nonempty (FaceReduction B t x d y π L ξ)

/-- The same face reduction at a prescribed scalar extension and root with
the canonical residue-field identification. -/
def SplitFaceResidueAtRoot : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
    (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))
    (x : ℚ ⊗[ℤ] E.Y),
    ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t →
    ∀ (d : ℕ) (y : E.Y), 0 < d → (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y →
    ∀ (π : Kˣ), normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ) →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
      [ValuativeExtension K L] (ξ : Lˣ),
      (ξ : L) ^ d = algebraMap K L (π : K) →
      Function.Bijective (residueMap K L) →
      Nonempty (FaceReduction B t x d y π L ξ)

end

end LinearAlgebraicGroups.Specs.ExceptionalSplitParahoricReduction
