import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbstractPairing

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.BorelNormalizer

open AdjointRepresentation (GroupPoints RelativeTangent constants dualMap)
open AbstractPairing (Root)
open BorelsAndChambers (IsPositiveSystem)
open CharacterDescent (Character)
open GeometricBorelConjugacy (ConjugatesSubgroups IsBorel IsKBorel)
open GeometricRadicals (IsMaximalTorus IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open SchemeDerivedGroup (FactorsThrough IsSubgroupOf)
open UnipotentRadicalIntersection (IsSchemeIntersection)
open LinearAlgebraicGroups.CocharacterDynamics (lieImage)

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- The zero-weight space in the tangent quotient of a geometric Borel
vanishes. A coset is fixed when its conjugation displacement lies in
the differential image of the Borel over every test algebra. -/
def LieQuotientZeroWeight : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsMaximalTorus T → IsBorel B → IsSubgroupOf T B →
      ∀ v : Lie k G.val,
        (∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
          let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
          let c := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
          ∃ w : RelativeTangent B.group R,
            w.toMul.val ≫ B.inclusion.hom.hom = c * p * c⁻¹ * p⁻¹) →
        v ∈ lieImage B

/-- The scheme normalizer of a geometric Borel is smooth and equals the Borel
as a closed subgroup scheme of the ambient reductive group. -/
def GeometricBorelNormalizer : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ B : ClosedSubgroup G.val, IsBorel B →
    ∀ N : ClosedSubgroup G.val,
      RepresentsSubgroup N (fun _ g ↦ Normalizes B.inclusion g) →
      Smooth N.group.X.hom ∧ SameSubgroup N B

/-- A Borel defined over the ground field represents its own scheme normalizer. -/
def GroundFieldBorelNormalizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ B : ClosedSubgroup G.val, IsKBorel B →
      RepresentsSubgroup B (fun _ g ↦ Normalizes B.inclusion g)

/-- The scheme intersection of a geometric Borel and the normalizer of a maximal
torus it contains is the torus. -/
def BorelNormalizerIntersection : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsMaximalTorus T → IsBorel B → IsSubgroupOf T B →
    ∀ N : ClosedSubgroup G.val,
      RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g) →
      IsSchemeIntersection {N, B} T

/-- In the conjugation action, any two Borels through the torus are related by
a normalizer point, and the full set of such points is one right torus coset. -/
def BorelConjugationSimplyTransitive (T : ClosedSubgroup G)
    (IsBorelSubgroup : ClosedSubgroup G → Prop) : Prop :=
  (∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ IsSubgroupOf T B) ∧
  ∀ B₁ B₂ : ClosedSubgroup G, IsBorelSubgroup B₁ → IsBorelSubgroup B₂ →
    IsSubgroupOf T B₁ → IsSubgroupOf T B₂ →
    ∃ g : 𝟙_ (SchemeOver k) ⟶ G.X,
      Normalizes T.inclusion g ∧ ConjugatesSubgroups g B₁ B₂ ∧
      ∀ g' : 𝟙_ (SchemeOver k) ⟶ G.X, Normalizes T.inclusion g' →
        (ConjugatesSubgroups g' B₁ B₂ ↔ FactorsThrough T (g⁻¹ * g'))

/-- The Weyl group acts simply transitively on geometric Borels containing
a maximal torus. -/
def GeometricWeylSimplyTransitiveOnBorels : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsMaximalTorus T →
      BorelConjugationSimplyTransitive T IsBorel

/-- Over the ground field, the Weyl group of a split maximal torus acts
simply transitively on the Borel subgroups containing it. -/
def WeylSimplyTransitiveOnBorels : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      BorelConjugationSimplyTransitive T IsKBorel

/-- The torus automorphism induced by a given rational normalizer point. -/
def InducesTorusConjugation (T : ClosedSubgroup G) (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (e : T.group ≅ T.group) : Prop :=
  (e.hom ≫ T.inclusion).hom.hom =
    (toUnit T.group.X ≫ g) * T.inclusion.hom.hom * (toUnit T.group.X ≫ g)⁻¹

/-- The action on positive systems is inverse pullback on the actual
characters of the torus. It preserves positive systems, and the points
sending any one system to another form one right torus coset. -/
def WeylSimplyTransitiveOnPositiveSystems : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      (∃ S : Set (Root T), IsPositiveSystem T S) ∧
      (∀ (S : Set (Root T)), IsPositiveSystem T S →
        ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, Normalizes T.inclusion g →
          ∃ (e : T.group ≅ T.group) (S' : Set (Root T)),
            InducesTorusConjugation T g e ∧ IsPositiveSystem T S' ∧
            (fun χ : Character T.group ↦ e.inv ≫ χ) '' (Subtype.val '' S) =
              Subtype.val '' S') ∧
      ∀ (S₁ S₂ : Set (Root T)), IsPositiveSystem T S₁ → IsPositiveSystem T S₂ →
        ∃ (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) (e : T.group ≅ T.group),
          Normalizes T.inclusion g ∧ InducesTorusConjugation T g e ∧
          (fun χ : Character T.group ↦ e.inv ≫ χ) '' (Subtype.val '' S₁) =
            Subtype.val '' S₂ ∧
          ∀ (g' : 𝟙_ (SchemeOver k) ⟶ G.val.X) (e' : T.group ≅ T.group),
            Normalizes T.inclusion g' → InducesTorusConjugation T g' e' →
              ((fun χ : Character T.group ↦ e'.inv ≫ χ) '' (Subtype.val '' S₁) =
                Subtype.val '' S₂ ↔ FactorsThrough T (g⁻¹ * g'))

end

end LinearAlgebraicGroups.Specs.BorelNormalizer
