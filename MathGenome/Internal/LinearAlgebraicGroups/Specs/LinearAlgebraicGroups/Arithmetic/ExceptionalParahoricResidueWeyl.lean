import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalParahoricResidueWeyl

open AbstractPairing (Datum)
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots)
open DatumAndWeyl (Identification)
open ExceptionalIwahoriCongruence (integralRing)
open ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open GeometricRadicals (IsReductive IsSplitTorus)
open IntegralSemisimpleModel (Model fibre forgetFibrePoint splitTorus)
open Pinning (BasedRootDatum transportCharacter)
open RankOneFlag (IsGeometricallyMaximal)

/-- The marking transports characters from the integral root datum to the residue torus. -/
noncomputable def markedCharacter {k : Type u} [Field k] {E : BasedRootDatum.{u}} {M : Model E}
    (F : MarkedFibre M k) {T : GroupScheme k}
    (τ : (fibre k).obj (splitTorus E) ≅ T) (z : E.X) : Character T :=
  transportCharacter (F.torusIso.symm ≪≫ τ)
    (Additive.toMul (F.realization.datumIso.val.weightEquiv z))

/-- The surviving Weyl group acts on the full marked lattice and its residue
normalizer sections are given by the signed integral wall words. -/
def MarkedResidueWeylComparison : Prop :=
  ∀ {k : Type u} [Field k] {E : BasedRootDatum.{u}} (M : Model E) (F : MarkedFibre M k)
    (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ (i : G.val ⟶ (fibre k).obj M.group), IsClosedImmersion i.hom.hom.left →
    ∀ (τ : (fibre k).obj (splitTorus E) ≅ T.group),
      τ.hom ≫ T.inclusion ≫ i = (fibre k).map M.torus →
    ∀ (S : Set E.I),
      (∀ a ∈ S, E.datum.reflectionPerm a a ∈ S) →
      (fun a => transportCharacter (F.torusIso.symm ≪≫ τ)
        (F.realization.datumIso.val.indexEquiv a).val) '' S = absoluteRoots T →
      (∀ a ∈ S, ∃ r : (fibre k).obj M.line.group ⟶ G.val,
        r ≫ i = (fibre k).map (M.root a)) →
    ∀ [IsCommMonObj T.group.X] (D : Datum T) (J : Identification D),
      let W := Subgroup.closure (RootPairing.weylGroup.ofIdx E.datum '' S)
      ∃ θ : W ≃* D.rootDatum.weylGroup,
        (∀ (w : W) (z : E.X),
          Additive.ofMul (markedCharacter F τ (w.val.val.weightEquiv z)) =
            (θ w).val.weightEquiv (Additive.ofMul (markedCharacter F τ z))) ∧
        ∀ (l : List E.I), (∀ a ∈ l, a ∈ S) →
          ∀ (w : W), w.val = (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod →
        ∃ n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X,
          n ≫ J.quotient.hom.hom = J.image.constantGroup.sectionPoint (J.labelEquiv (θ w)) ∧
          let R := CommAlgCat.of k k
          let Y := (testSpec k).obj (Opposite.op R)
          forgetFibrePoint M.group R
              (toUnit Y ≫ n ≫ J.normalizer.inclusion.hom.hom ≫ i.hom.hom) =
            markedWeylWord M.toIntegralMarking (integralRing k) l

end LinearAlgebraicGroups.Specs.ExceptionalParahoricResidueWeyl
