import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalResidueCentralizer

open AdjointRepresentation (GroupPoints)
open CharacterPairing (absoluteRoots characterValue)
open DiagonalizableGroups (diagonalGroup rootsOfUnityPoints)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open IntegralSemisimpleModel
  (Integers Model fibre splitTorus integerAlgebra forgetFibrePoint torusPoint cocharacter TorusValues)
open Pinning (BasedRootDatum RootCoordinate transportCharacter)
open RankOneFlag (IsGeometricallyMaximal)
open RationalRealization (Realization)
open SchemeDerivedGroup (IsSubgroupOf)

attribute [local instance] integerAlgebra

noncomputable section

/-- The scheme of `d`th roots of unity in its cyclic diagonalizable presentation. -/
abbrev cyclicGroup (k : Type u) [Field k] (d : ℕ) [NeZero d] : GroupScheme k :=
  (diagonalGroup k (ULift.{u} (Multiplicative (ZMod d)))).val

/-- The root evaluation on the rational cocharacter space. -/
abbrev rootValue (E : BasedRootDatum.{u}) (a : E.I) (v : ℚ ⊗[ℤ] E.Y) : ℚ :=
  RootData.extendFunctional ℚ (E.datum.root' a) v

/-- The roots detected by the cyclic scaling cocharacter. -/
def survivingRoots (E : BasedRootDatum.{u}) (d : ℕ) (y : E.Y) : Set E.I :=
  {a | (d : ℤ) ∣ E.datum.toLinearMap (E.datum.root a) y}

/-- The connected centralizer, its split maximal torus, and the Borel selected
by the regular direction on its roots. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {E : BasedRootDatum.{u}} (M : Model E)
    (d : ℕ) (y : E.Y) (v : ℚ ⊗[ℤ] E.Y) (hd : 0 < d),
    letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
    (∀ a ∈ survivingRoots E d y, rootValue E a v ≠ 0) →
    ∀ (A : RootGroups.AdditiveLine k) (F : Realization E A)
      (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
      (t : (fibre k).obj (splitTorus E) ≅ F.pinned.pair.T.group)
      (z : ∀ a : E.I, RootCoordinate A F.pinned.pair.T
        (F.pinned.roots (F.datumIso.val.indexEquiv a)).val (F.datumIso.val.indexEquiv a).val),
      (fibre k).map M.torus ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion →
      (∀ a : E.base.support, z a.val = F.pinned.pin (F.simpleRoot a)) →
      (∀ (R : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus E)) R)
        (w : TorusValues E (CommAlgCat.of Integers.{u} R)),
        forgetFibrePoint (splitTorus E) R s = torusPoint E (CommAlgCat.of Integers.{u} R) w →
        ∀ x : E.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
          (s ≫ t.hom.hom.hom) = (w (Multiplicative.ofAdd x) : R)) →
      (∀ (a : E.I) (R : TestAlgebra k) (r : R),
        forgetFibrePoint M.group R
          (RootGroups.rootPoint ((z a).val.hom ≫
            (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion ≫ e.inv) R r) =
          M.line.point (CommAlgCat.of Integers.{u} R) r ≫ (M.root a).hom.hom) →
      ∃ (unitPoints : (groupPointsFunctor k).obj (cyclicGroup k d) ≅ rootsOfUnityPoints k d)
        (i : cyclicGroup k d ⟶ (fibre k).obj M.group)
        (C : ClosedSubgroup ((fibre k).obj M.group)) (H : ClosedSubgroup C.group),
        (∀ (R : TestAlgebra k) (r : GroupPoints (cyclicGroup k d) R),
          let s : rootsOfUnity d R := unitPoints.hom.app R r
          forgetFibrePoint M.group R (r ≫ i.hom.hom) =
            torusPoint E (CommAlgCat.of Integers.{u} R)
              (cocharacter E y (CommAlgCat.of Integers.{u} R) s.val) ≫ M.torus.hom.hom) ∧
        RepresentsSubgroup C (fun _ g => Centralizes i g) ∧
        Smooth C.group.X.hom ∧ IsOpenImmersion H.inclusion.hom.hom.left ∧
        Set.range H.inclusion.hom.hom.left = connectedComponent (η[C.group.X].left
          (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ∧
        ∃ (ha : IsAffine H.group.X.left) (hf : LocallyOfFiniteType H.group.X.hom)
          (hq : QuasiCompact H.group.X.hom),
          IsReductive ⟨H.group, ha, hf, hq⟩ ∧
          ∃ (T : ClosedSubgroup H.group) (torusComparison : (fibre k).obj (splitTorus E) ≅ T.group),
            torusComparison.hom ≫ T.inclusion ≫ H.inclusion ≫ C.inclusion = (fibre k).map M.torus ∧
            IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
            absoluteRoots T =
              (fun a : E.I => transportCharacter (t.symm ≪≫ torusComparison)
                (F.datumIso.val.indexEquiv a).val) '' survivingRoots E d y ∧
            (∀ a : E.I,
              (∃ h : (fibre k).obj M.line.group ⟶ H.group,
                h ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M.root a)) ↔
                a ∈ survivingRoots E d y) ∧
            ∃ B : ClosedSubgroup H.group, IsKBorel B ∧ IsSubgroupOf T B ∧
              ∀ a : E.I,
                (∃ h : (fibre k).obj M.line.group ⟶ B.group,
                  h ≫ B.inclusion ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M.root a)) ↔
                  a ∈ survivingRoots E d y ∧ 0 < rootValue E a v

end

end LinearAlgebraicGroups.Specs.ExceptionalResidueCentralizer
