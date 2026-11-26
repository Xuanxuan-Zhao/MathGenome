import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding

namespace LinearAlgebraicGroups.Specs.ExceptionalParahoricPointReduction

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
open ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open ExceptionalMarkedRootDescent (MarkedFibre)
open ExceptionalIwahoriImageComparison (MarkedCentralCover)
open AdjointRepresentation (GroupPoints)
open GeometricRadicals (IsReductive IsSplitReductive IsSplitTorus IsMaximalTorus)
open GeometricBorelConjugacy (IsKBorel)

attribute [local instance] integerAlgebra

noncomputable section

section PointReduction

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "A" => ApartmentRoots.split E.datum ℚ
local notation "P(" T ")" => parahoric Y.ad T

/-- The scaled parahoric, its marked reduction and the associated rational flags. -/
structure PointReduction
    (t : Weights (ApartmentRoots.SimpleWall A p')) (y : E.Y)
    (L : Type u) [Field L] [Algebra K L] [ValuativeRel L]
    (ξ : Lˣ)
    (C : ClosedSubgroup ((fibre (residue L)).obj M'.group))
    (H : ClosedSubgroup C.group) (Bψ : ClosedSubgroup H.group) where
  integral : P(cotype t) →* IntegralPoints M'.group (localIntegers L)
  scale (g : P(cotype t)) :
    let R := integralRing L
    let s := torusPoint E R (cocharacter E y R ξ) ≫ M'.torus.hom.hom
    changeRingHom M'.group (localIntegersInclusion L) (integral g) =
      s * scalarPoints M' (algebraMap K L) (g : FieldPoints M' K) * s⁻¹
  reduction : P(cotype t) →*
    GroupPoints H.group (CommAlgCat.of (residue L) (residue L))
  reduction_eq (g : P(cotype t)) :
    forgetFibrePoint M'.group (CommAlgCat.of (residue L) (residue L))
      (reduction g ≫ H.inclusion.hom.hom ≫ C.inclusion.hom.hom) =
        changeRingHom M'.group (residueHom (localIntegers L)) (integral g)
  reduction_surjective : Function.Surjective reduction
  preimage_borel (g : P(cotype t)) :
    (∃ b : GroupPoints Bψ.group (CommAlgCat.of (residue L) (residue L)),
      b ≫ Bψ.inclusion.hom.hom = reduction g) ↔ (g : FieldPoints M' K) ∈ Y.ad.I
  iwahori_image (b : GroupPoints Bψ.group (CommAlgCat.of (residue L) (residue L))) :
    ∃ g : P(cotype t), (g : FieldPoints M' K) ∈ Y.ad.I ∧
      reduction g = b ≫ Bψ.inclusion.hom.hom
  flags : QuotientEmbedding.Presentation Bψ
  flag_surjective : Function.Surjective (fun g : GroupPoints H.group
      (CommAlgCat.of (residue L) (residue L)) => g ≫ flags.projection)
  flag_fibres (a b : GroupPoints H.group (CommAlgCat.of (residue L) (residue L))) :
    a ≫ flags.projection = b ≫ flags.projection ↔
      ∃ r : GroupPoints Bψ.group (CommAlgCat.of (residue L) (residue L)),
        r ≫ Bψ.inclusion.hom.hom = a⁻¹ * b

end PointReduction

/-- Reduction of the marked face parahoric at a prescribed uniformizer root,
given the reductive residue subgroup and its marked root and Borel data. -/
def SplitParahoricPointReduction : Prop :=
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
    let k := residue L
    let A := ApartmentRoots.split E.datum ℚ
    ∀ (C : ClosedSubgroup ((fibre k).obj M'.group)) (H : ClosedSubgroup C.group)
      (hAff : IsAffine H.group.X.left) (hLft : LocallyOfFiniteType H.group.X.hom)
      (hQc : QuasiCompact H.group.X.hom)
      (hRed : IsReductive ⟨H.group, hAff, hLft, hQc⟩)
      (T : ClosedSubgroup H.group)
      (τ : (fibre k).obj (splitTorus E) ≅ T.group)
      (hMark : τ.hom ≫ T.inclusion ≫ H.inclusion ≫ C.inclusion = (fibre k).map M'.torus)
      (hSplit : IsSplitTorus T.group)
      (hMax : ∃ h : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
          IsMaximalTorus (GeometricRadicals.baseChangedSubgroup (AlgebraicClosure k) T h))
      (F : MarkedFibre M' k)
      (hCharacters : CharacterPairing.absoluteRoots T =
        (fun a : E.I => Pinning.transportCharacter (F.torusIso.symm ≪≫ τ)
          (F.realization.datumIso.val.indexEquiv a).val) ''
            {a | ∃ j : ℤ, A.root a x = j})
      (hRoot : ∀ a : E.I,
        (∃ r : (fibre k).obj M'.line.group ⟶ H.group,
          r ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M'.root a)) ↔
          ∃ j : ℤ, A.root a x = j)
      (Bψ : ClosedSubgroup H.group)
      (hBorel : IsKBorel Bψ) (hBT : SchemeDerivedGroup.IsSubgroupOf T Bψ)
      (hBorelRoot : ∀ a : E.I,
        (∃ r : (fibre k).obj M'.line.group ⟶ Bψ.group,
          r ≫ Bψ.inclusion ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M'.root a)) ↔
          ∃ j : ℤ, A.root a x = j ∧ A.positive p' (a, -j)),
      Nonempty (PointReduction (Y := Y) t y L ξ C H Bψ)

end

end LinearAlgebraicGroups.Specs.ExceptionalParahoricPointReduction
