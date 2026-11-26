import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RationalContraction

open CharacterDescent (Cocharacter)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open AdjointRepresentation (GroupPoints)
open ClosedHomogeneousOrbits (vectorSpace)
open LinearAlgebraicGroups.CocharacterDynamics

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k} {X : SchemeOver k}

abbrev groundField (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

/-- The spectrum of the ground algebra is the monoidal unit over the field. -/
def groundPointIso (k : Type u) [Field k] :
    𝟙_ (SchemeOver k) ≅ (testSpec k).obj (.op (groundField k)) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change 𝟙 (Spec (CommRingCat.of k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    rw [Category.id_comp]
    exact Spec.map_id _)

/-- The action of the cocharacter on a point over the punctured affine line. -/
def actionCurve (a : ModObj G.X X) (cochar : Cocharacter G)
    {R : TestAlgebra k} (x : Points X R) : Points X (laurentAlgebra R) :=
  lift (cocharacterPoint cochar _ (laurentParameter R)) (mapPoints (laurentConstants R) x) ≫
    a.smul

/-- The scheme-theoretic limit of the cocharacter action at zero. -/
def ActionHasLimit (a : ModObj G.X X) (cochar : Cocharacter G)
    {R : TestAlgebra k} (x x₀ : Points X R) : Prop :=
  ∃ c : Points X (polynomialAlgebra R),
    mapPoints (polynomialToLaurent R) c = actionCurve a cochar x ∧
      mapPoints (polynomialEvaluate R 0) c = x₀

/-- The conjugate by `g` of the image of the cocharacter is a split
one-dimensional torus in the scheme stabilizer of `x`. -/
def HasConjugateSplitTorus (a : ModObj G.X X) (cochar : Cocharacter G)
    (g : GroupPoints G (groundField k)) (x : Points X (groundField k)) : Prop :=
  ∃ (S : ClosedSubgroup G) (p : Cocharacter S.group),
    Nonempty (S.group ≅ specGroup (groupAlgebra k IntegerCharacters)) ∧
    Surjective p.hom.hom.left ∧
    (p ≫ S.inclusion).hom.hom =
      (toUnit _ ≫ (groundPointIso k).hom ≫ g) * cochar.hom.hom * (toUnit _ ≫ (groundPointIso k).hom ≫ g)⁻¹ ∧
    ∀ (T : SchemeOver k) (s : T ⟶ S.group.X),
      Stabilizes a.smul ((groundPointIso k).hom ≫ x) (s ≫ S.inclusion.hom.hom)

/-- Each rational point is the translate of its limit by a rational point of
the contracting subgroup, expressed by its polynomial limit condition. -/
def ContractsRationally (a : ModObj G.X X) : Prop :=
  ∀ (cochar : Cocharacter G) (x x₀ : Points X (groundField k)),
    ActionHasLimit a cochar x x₀ →
    ∃ g : GroupPoints G (groundField k), HasLimit cochar g 1 ∧
      lift g x₀ ≫ a.smul = x ∧
      (cochar.hom.hom ≠ toUnit _ ≫ η[G.X] → HasConjugateSplitTorus a cochar g x)

/-- Rational contraction for a given affine smooth right homogeneous quotient.
The two equivariance equations identify the quotient map with the orbit map of
the identity coset. -/
def QuotientContractsRationally : Prop :=
  ∀ {k : Type u} [Field k] (P : AffineAlgebraicGroup k) {H : ClosedSubgroup P.val}
    (Q : QuotientEmbedding.Presentation H) {V : SchemeOver k}
    (a : ModObj P.val.X V) (b : ModObj P.val.X Q.scheme) (j : Q.scheme ⟶ V),
    GeometricRadicals.IsSemisimple (Unipotent.closedSubgroupAlgebraicGroup H) →
    IsAffine Q.scheme.left → Smooth Q.projection.left → IsClosedImmersion j.left →
    b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul →
    Q.projection ≫ j = SmoothOrbit.orbitMap a (η[P.val.X] ≫ Q.projection ≫ j) →
    ContractsRationally b

/-- A closed rational linear model of the indicated right quotient has the
rational contraction property, with the prescribed scheme stabilizer at the
identity coset. -/
def RationalContraction : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (m : ℕ) (P : AffineAlgebraicGroup k)
    (_ : (groupPointsFunctor k).obj P.val ≅
      StandardGroups.specialLinearPoints k (ULift.{u} (Fin m)))
    (H : ClosedSubgroup P.val),
    GeometricRadicals.IsSemisimple (Unipotent.closedSubgroupAlgebraicGroup H) →
    ∃ (Q : QuotientEmbedding.Presentation H)
      (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (ρ : RootWeightAction.Representation P.val I) (a : ModObj P.val.X (vectorSpace k I))
      (b : ModObj P.val.X Q.scheme) (j : Q.scheme ⟶ vectorSpace k I),
      IsAffine Q.scheme.left ∧ HomogeneousQuotient.IsQuotientTorsor Q ∧
      Smooth Q.projection.left ∧ IsClosedImmersion j.left ∧
      (∀ (R : TestAlgebra k) (g : Points P.val.X R) (v : I → R),
        lift g (ClosedHomogeneousOrbits.vectorPoint R v) ≫ a.smul =
          ClosedHomogeneousOrbits.vectorPoint R (RootWeightAction.act ρ R g v)) ∧
      b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul ∧
      Q.projection ≫ j = SmoothOrbit.orbitMap a (η[P.val.X] ≫ Q.projection ≫ j) ∧
      RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul (η[P.val.X] ≫ Q.projection ≫ j) g) ∧
      ContractsRationally b

end

end LinearAlgebraicGroups.Specs.RationalContraction
