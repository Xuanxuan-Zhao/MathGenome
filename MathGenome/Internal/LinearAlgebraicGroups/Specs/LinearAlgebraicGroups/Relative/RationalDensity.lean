import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.Relative.RationalDensity

open GeometricRadicals (GeometricGroup IsReductive IsTorus)
open SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

variable {k : Type u} [Field k]

/-- The point of the scalar extension obtained from a rational section. -/
def rationalPointOver (K : Type u) [Field K] [Algebra k K] {X : SchemeOver k}
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) : ((baseChange k K).obj X).left :=
  let lift : Spec (CommRingCat.of K) ⟶ ((baseChange k K).obj X).left :=
    pullback.lift (fieldSpecMap k K ≫ x.left) (𝟙 _) (by
      rw [Category.assoc, Over.w x]
      simp)
  lift (IsLocalRing.closedPoint K)

/-- Density of the image of the rational points in the Zariski topology
after extension to the algebraic closure. -/
def GeometricallyDenseRationalPoints (X : SchemeOver k) : Prop :=
  Dense (Set.range (rationalPointOver (AlgebraicClosure k) (X := X)))

/-- Every closed subgroup containing all closed tori defined over k
is the whole group. -/
def GeneratedByRationalTori (G : AffineAlgebraicGroup k) : Prop :=
  ∀ H : ClosedSubgroup G.val,
    (∀ T : ClosedSubgroup G.val, IsTorus T.group → IsSubgroupOf T H) →
    IsIso H.inclusion

/-- The scalar extensions of the tori defined over k generate the whole
geometric group as a closed subgroup scheme. -/
def GeometricallyGeneratedByRationalTori (G : AffineAlgebraicGroup k) : Prop :=
  ∀ H : ClosedSubgroup (GeometricGroup G).val,
    (∀ T : ClosedSubgroup G.val, IsTorus T.group →
      ∃ i : (groupBaseChange k (AlgebraicClosure k)).obj T.group ⟶ H.group,
        i ≫ H.inclusion = (groupBaseChange k (AlgebraicClosure k)).map T.inclusion) →
    IsIso H.inclusion

/-- Connected reductive groups over infinite fields are generated as closed
groups by the tori defined over the ground field, also after geometric base change. -/
def ReductiveGeneratedByRationalTori : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : AffineAlgebraicGroup k),
    IsReductive G → GeneratedByRationalTori G ∧ GeometricallyGeneratedByRationalTori G

/-- The rational points of a torus over an infinite field are geometrically dense. -/
def TorusRationalPointsDense : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (T : AffineAlgebraicGroup k),
    IsTorus T.val → GeometricallyDenseRationalPoints T.val.X

/-- The rational points of a connected reductive group over an infinite field
are geometrically dense. -/
def ReductiveRationalPointsDense : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : AffineAlgebraicGroup k),
    IsReductive G → GeometricallyDenseRationalPoints G.val.X

end

end LinearAlgebraicGroups.Specs.Relative.RationalDensity
