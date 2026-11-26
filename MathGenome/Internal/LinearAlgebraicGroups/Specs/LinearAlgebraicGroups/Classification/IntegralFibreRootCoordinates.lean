import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.IntegralFibreRootCoordinates

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots characterValue)
open GeometricRadicals (IsReductive IsSplitTorus)
open IntegralCentralQuotient (ReductiveFibres)
open IntegralSemisimpleModel
open OrderedRootProducts (Enumerates)
open Pinning (BasedRootDatum)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (HasScalarAction IsRootSubgroup rootPoint)

noncomputable section

attribute [local instance] integerAlgebra

/-- The affine algebraic group of the field fibre of a smooth affine integral group. -/
def fibreAlgebraicGroup (k : Type u) [Field k] (G : IntegralGroup.{u})
    [IsAffine G.X.left] [Smooth G.X.hom] : AffineAlgebraicGroup k := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k))
  letI : QuasiCompact G.X.hom := inferInstance
  exact ⟨(fibre k).obj G,
    inferInstanceAs (IsAffine (Limits.pullback G.X.hom f)),
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.X.hom f)),
    inferInstanceAs (QuasiCompact (Limits.pullback.snd G.X.hom f))⟩

/-- The marked torus and root coordinates identify the actual absolute roots in
each field fibre, with their actions on the standard additive parameter. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}) (G : IntegralGroup.{u}) [IsAffine G.X.left] [Smooth G.X.hom]
      (L : AdditiveLine.{u}) (t : splitTorus D ⟶ G) (x : D.I → (L.group ⟶ G)),
    IsClosedImmersion t.hom.hom.left →
    (∀ a, IsClosedImmersion (x a).hom.hom.left) →
    ReductiveFibres t →
    (∀ (R : IntegralAlgebra.{u}) (v : TorusValues D R) (a : D.I) (z : R),
      let g := torusPoint D R v ≫ t.hom.hom
      g * (L.point R z ≫ (x a).hom.hom) * g⁻¹ =
        L.point R ((v (Multiplicative.ofAdd (D.datum.root a)) : R) * z) ≫ (x a).hom.hom) →
    ∀ (negative positive : List D.I),
      Enumerates negative {i | ¬ D.base.IsPos i} →
      Enumerates positive {i | D.base.IsPos i} →
      IsOpenImmersion (cellMap L t x negative positive).left →
    ∀ (k : Type u) [Field k],
      let H := fibreAlgebraicGroup k G
      ∃ (hT : IsClosedImmersion ((fibre k).map t).hom.hom.left)
        (A : RootGroups.AdditiveLine k) (e : A.group ≅ (fibre k).obj L.group)
        (χ : D.X ≃ₗ[ℤ] Additive (Character ((fibre k).obj (splitTorus D)))),
        let T : ClosedSubgroup H.val := ⟨_, (fibre k).map t, hT⟩
        IsReductive H ∧ IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
        (∀ (R : TestAlgebra k) (z : R),
          forgetFibrePoint L.group R (rootPoint e.hom R z) =
            L.point (CommAlgCat.of Integers.{u} R) z) ∧
        (∀ (R : TestAlgebra k) (s : GroupPoints T.group R)
            (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
          forgetFibrePoint (splitTorus D) R s =
            torusPoint D (CommAlgCat.of Integers.{u} R) v →
          ∀ w : D.X, characterValue (Additive.toMul (χ w)) R s =
            (v (Multiplicative.ofAdd w) : R)) ∧
        ∃ b : D.I ≃ ↥(absoluteRoots T),
          ∀ a : D.I, (b a).val = Additive.toMul (χ (D.datum.root a)) ∧
            let f := e.hom ≫ (fibre k).map (x a)
            ∃ hf : IsClosedImmersion f.hom.hom.left,
              IsRootSubgroup T ⟨A.group, f, hf⟩ (b a).val ∧ HasScalarAction T (b a).val f

end

end LinearAlgebraicGroups.Specs.IntegralFibreRootCoordinates
