import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.TorusLimitFactorRestriction

open StandardGroups Unipotent

/-- For a closed matrix realization with a diagonal split torus, the negative,
positive and zero weight unitriangular factors of a point of the group are
themselves points of the group. The signs are taken relative to an arbitrary
cocharacter of the torus, and the assertion is over every test algebra. -/
def FactorRestriction : Prop :=
  ∀ {k : Type u} [Field k] {n r : ℕ} {G H : AffineAlgebraicGroup k}
    (j : G.val ⟶ H.val) (T : ClosedSubgroup G.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} r))
    (m : Index.{u} n → Index.{u} r → ℤ) (l : Index.{u} r → ℤ),
    IsClosedImmersion j.hom.hom.left →
    (∀ (R : TestAlgebra k) (a : Points T.group.X R) (i j' : Index.{u} n),
      (e.hom.app R (((groupPointsFunctor k).map (T.inclusion ≫ j)).app R a)).val i j' =
        if i = j' then
          (↑(∏ s : Index.{u} r, (t.hom.app R a) s ^ m i s) : R)
        else 0) →
    ∀ (R : TestAlgebra k),
      let w (i : Index.{u} n) : ℤ := ∑ s : Index.{u} r, m i s * l s
      let image : Set (Matrix.GeneralLinearGroup (Index.{u} n) R) :=
        Set.range (fun g : Points G.val.X R ↦
          e.hom.app R (((groupPointsFunctor k).map j).app R g))
      let supported (q : Index.{u} n → Index.{u} n → Prop)
          (x : upperUnitriangular (Index.{u} n) R) : Prop :=
        ∀ i j', ¬ (i < j' ∧ q i j') → (x.val.val - 1) i j' = 0
      ∀ a b z : upperUnitriangular (Index.{u} n) R,
        supported (fun i j' ↦ w i < w j') a →
        supported (fun i j' ↦ w j' < w i) b →
        supported (fun i j' ↦ w i = w j') z →
        (a * b * z).val ∈ image →
        a.val ∈ image ∧ b.val ∈ image ∧ z.val ∈ image

end LinearAlgebraicGroups.Specs.TorusLimitFactorRestriction
