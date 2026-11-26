import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbstractPairing
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.WeylScheme
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.DatumAndWeyl

open AbstractPairing (Datum)
open CharacterDescent (Character Cocharacter)
open GeometricRadicals (IsReductive IsSplitTorus)
open NormalizerLatticeAction (SplitImage)
open RankOneFlag (IsGeometricallyMaximal)
open Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)

/-- The reflection-generated Weyl group gives the labels of the finite constant
normalizer quotient. The label action comes from scheme conjugation and agrees
with the root datum action on both lattices. -/
structure Identification {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (D : Datum T) where
  normalizer : ClosedSubgroup G.val
  torusInclusion : T.group ⟶ normalizer.group
  torusClosed : IsClosedImmersion torusInclusion.hom.hom.left
  scheme : AffineAlgebraicGroup k
  quotient : normalizer.group ⟶ scheme.val
  representsNormalizer : RepresentsSubgroup normalizer (fun _ g ↦ Normalizes T.inclusion g)
  inclusion_eq : torusInclusion ≫ normalizer.inclusion = T.inclusion
  isQuotient : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup normalizer)
    ⟨T.group, torusInclusion, torusClosed⟩ quotient
  finite : IsFinite scheme.val.X.hom
  etale : Etale scheme.val.X.hom
  image : SplitImage T.inclusion normalizer.inclusion quotient
  labelEquiv : D.rootDatum.weylGroup ≃* image.labels
  characterAction : ∀ (w : D.rootDatum.weylGroup) (χ : Character T.group),
    w.val.weightEquiv (Additive.ofMul χ) = Additive.ofMul ((labelEquiv w).val χ)
  cocharacterAction : ∀ (w : D.rootDatum.weylGroup) (cochar : Cocharacter T.group),
    w.val.coweightEquiv.symm (Additive.ofMul cochar) =
      Additive.ofMul (cochar ≫ (image.conjugation (labelEquiv w)).hom)

/-- The actual finite reduced root datum of a split connected reductive pair
has Weyl group naturally identified with the constant scheme W(G,T). -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ D : Datum T, Nonempty (Identification D)

end LinearAlgebraicGroups.Specs.DatumAndWeyl
