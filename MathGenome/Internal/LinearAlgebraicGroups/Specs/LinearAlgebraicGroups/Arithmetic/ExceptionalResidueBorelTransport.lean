import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalResidueBorelTransport
noncomputable section

open AdjointRepresentation (GroupPoints)
open CharacterPairing (absoluteRoots)
open ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom)
open ExceptionalMarkedRootDescent (MarkedFibre markedRootPoint markedWeylWord weylWordPerm)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open IntegralSemisimpleModel
open Pinning (BasedRootDatum transportCharacter)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}} {M : Model D}

/-- The scalar embedding is precomposed by the inverse field automorphism. -/
def twistAlgebra (sigma : k ≃+* k) (R : TestAlgebra k) : TestAlgebra k :=
  @CommAlgCat.of k _ R R.commRing (((algebraMap k R).comp sigma.symm.toRingHom).toAlgebra)

/-- The ambient labelled root character, transported to the torus of the residue group. -/
def rootCharacter (C : MarkedFibre M k) {H : GroupScheme k} (T : ClosedSubgroup H)
    (t : (fibre k).obj (splitTorus D) ≅ T.group) (a : D.I) :
    CharacterDescent.Character T.group :=
  transportCharacter (C.torusIso.symm ≪≫ t) (C.realization.datumIso.val.indexEquiv a).val

/-- The map from Borel points into the integral model on the underlying test ring. -/
def borelPoint {H : GroupScheme k} (j : H ⟶ (fibre k).obj M.group)
    (B : ClosedSubgroup H) (R : TestAlgebra k) (b : GroupPoints B.group R) :
    IntegralPoints M.group (integralRing R) :=
  forgetFibrePoint M.group R (b ≫ (B.inclusion ≫ j).hom.hom)

/-- The correcting point over the residue field, in the specified torus-times-word order. -/
def correction (M : Model D) (l : List D.I) (v : TorusValues D (integralRing k)) :
    IntegralPoints M.group (integralRing k) :=
  (torusPoint D (integralRing k) v ≫ M.torus.hom.hom) *
    markedWeylWord M.toIntegralMarking (integralRing k) l

set_option backward.isDefEq.respectTransparency false in
/-- The corrected pinned operator preserves the marked residue Borel on every
test algebra, with the coefficient action implemented by twisting its scalar map. -/
def MarkedBorelTransport : Prop :=
  ∀ {k : Type u} [Field k] {D : BasedRootDatum.{u}} (M : Model D) (C : MarkedFibre M k)
    (H : AffineAlgebraicGroup k) (_ : IsReductive H)
    (j : H.val ⟶ (fibre k).obj M.group) (_ : IsClosedImmersion j.hom.hom.left)
    (T B : ClosedSubgroup H.val) (_ : IsSplitTorus T.group) (_ : IsGeometricallyMaximal T)
    (_ : IsKBorel B) (_ : IsSubgroupOf T B)
    (t : (fibre k).obj (splitTorus D) ≅ T.group)
    (_ : t.hom ≫ T.inclusion ≫ j = (fibre k).map M.torus)
    (Ψ Ψpos : Set D.I)
    (_ : absoluteRoots T = rootCharacter C T t '' Ψ)
    (_ : ∀ a, (∃ r : (fibre k).obj M.line.group ⟶ H.val,
      r ≫ j = (fibre k).map (M.root a)) ↔ a ∈ Ψ)
    (_ : ∀ a, (∃ r : (fibre k).obj M.line.group ⟶ B.group,
      r ≫ B.inclusion ≫ j = (fibre k).map (M.root a)) ↔ a ∈ Ψpos)
    (δ : Aut M.group) (diagram : D.datum.Equiv D.datum)
    (_ : ∀ (S : IntegralAlgebra.{u}) (s : TorusValues D S),
      (torusPoint D S s ≫ M.torus.hom.hom) ≫ δ.asIso.hom.hom.hom =
        torusPoint D S
          (s.comp diagram.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative) ≫
            M.torus.hom.hom)
    (_ : ∀ a : D.I, ∃ ε : Integers.{u}ˣ, ∀ (S : IntegralAlgebra.{u}) (z : S),
      markedRootPoint M.toIntegralMarking S a z ≫ δ.asIso.hom.hom.hom =
        markedRootPoint M.toIntegralMarking S (diagram.indexEquiv a)
          (algebraMap Integers.{u} S (ε : Integers.{u}) * z))
    (l : List D.I) (v : TorusValues D (integralRing k))
    (_ : diagram.indexEquiv.trans (weylWordPerm l) '' Ψpos = Ψpos)
    (R : TestAlgebra k) (sigma : k ≃+* k) (z : IntegralPoints M.group (integralRing R)),
    let R' := twistAlgebra sigma R
    let n := changeRingHom M.group (integralRingMap (algebraMap k R')) (correction M l v)
    let z' : IntegralPoints M.group (integralRing R') := z ≫ δ.asIso.hom.hom.hom
    z ∈ Set.range (borelPoint j B R) ↔ n * z' * n⁻¹ ∈ Set.range (borelPoint j B R')

end

end LinearAlgebraicGroups.Specs.ExceptionalResidueBorelTransport
