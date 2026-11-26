import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.BruhatOrbitParametrization

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open OrderedRootProducts (Enumerates Parametrizes RootSubgroupFamily)
open QuotientEmbedding (Presentation)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- Conjugation of a family of group elements by a rational point. -/
def conjugatePoint (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {Y : SchemeOver k}
    (g : Y ⟶ G.val.X) : Y ⟶ G.val.X :=
  (toUnit Y ≫ n) * g * (toUnit Y ≫ n)⁻¹

/-- Point families in the intersection of a subgroup and a conjugate subgroup. -/
def IsConjugateIntersection (A B H : ClosedSubgroup G.val)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) : Prop :=
  ∀ (Y : SchemeOver k) (g : Y ⟶ G.val.X),
    g ∈ SubgroupSections H Y ↔
      g ∈ SubgroupSections A Y ∧ conjugatePoint n⁻¹ g ∈ SubgroupSections B Y

/-- A lift to the scheme normalizer of the given root-datum Weyl element. -/
def IsRepresentative {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : Datum T}
    (I : Identification D) (w : D.rootDatum.weylGroup)
    (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) : Prop :=
  n ≫ I.quotient.hom.hom = I.image.constantGroup.sectionPoint (I.labelEquiv w)

/-- The product parametrization holds in every list order. -/
def OrderedParametrization {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (S : Set (Root T)) (H : ClosedSubgroup G.val) : Prop :=
  ∀ l : List (Root T), Enumerates l S → Parametrizes U l H.inclusion.hom.hom

/-- A point of the quotient over a field extension is fixed if its entire torus
orbit over that field is constant. The test scheme is the spectrum of that field. -/
def FixedOver {T : ClosedSubgroup G.val} {X Y : SchemeOver k}
    (a : ModObj G.val.X X) (x : Y ⟶ X) : Prop :=
  lift (fst T.group.X Y ≫ T.inclusion.hom.hom) (snd T.group.X Y ≫ x) ≫ a.smul =
    snd T.group.X Y ≫ x

/-- An orbit and its inverse image in the group, with their specified multiplication maps. -/
structure Cell {T B : ClosedSubgroup G.val} (Q : Presentation B)
    (a : ModObj G.val.X Q.scheme) (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (U : ClosedSubgroup G.val) where
  orbit : SchemeOver k
  orbitInclusion : orbit ⟶ Q.scheme
  orbitImmersion : IsImmersion orbitInclusion.left
  projection : B.group.X ⟶ orbit
  projection_eq : projection ≫ orbitInclusion =
    lift B.inclusion.hom.hom (toUnit B.group.X ≫ n ≫ Q.projection) ≫ a.smul
  orbitSurjective : Surjective projection.left
  orbitIso : U.group.X ≅ orbit
  orbitIso_eq : orbitIso.hom ≫ orbitInclusion =
    (U.inclusion.hom.hom * (toUnit U.group.X ≫ n)) ≫ Q.projection
  stabilizer : ClosedSubgroup B.group
  representsStabilizer : RepresentsSubgroup stabilizer (fun Y b ↦
    lift (b ≫ B.inclusion.hom.hom) (toUnit Y ≫ n ≫ Q.projection) ≫ a.smul =
      toUnit Y ≫ n ≫ Q.projection)
  quotientIso : rightQuotientSheaf stabilizer ≅ schemeFppfSheaf orbit
  quotientProjection : rightQuotientProjection stabilizer ≫ quotientIso.hom =
    (fppfOver k).uliftYoneda.map projection
  doubleOrbit : SchemeOver k
  doubleOrbitInclusion : doubleOrbit ⟶ G.val.X
  doubleOrbitImmersion : IsImmersion doubleOrbitInclusion.left
  toOrbit : doubleOrbit ⟶ orbit
  isInverseImage : IsPullback doubleOrbitInclusion toOrbit Q.projection orbitInclusion
  doubleOrbitIso : U.group.X ⊗ B.group.X ≅ doubleOrbit
  doubleOrbitIso_eq : doubleOrbitIso.hom ≫ doubleOrbitInclusion =
    (fst _ _ ≫ U.inclusion.hom.hom) *
      (toUnit (U.group.X ⊗ B.group.X) ≫ n) * (snd _ _ ≫ B.inclusion.hom.hom)
  doubleOrbitSections : ∀ (Y : SchemeOver k) (g : Y ⟶ G.val.X),
    (∃ c : Y ⟶ doubleOrbit, c ≫ doubleOrbitInclusion = g) ↔
      ∃ b₁ b₂ : Y ⟶ B.group.X,
        (b₁ ≫ B.inclusion.hom.hom) * (toUnit Y ≫ n) * (b₂ ≫ B.inclusion.hom.hom) = g
  uniqueGeometricFixedPoint :
    ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
      (y : Over.mk (fieldSpecMap k K) ⟶ orbit),
        FixedOver (T := T) a (y ≫ orbitInclusion) ↔
          y ≫ orbitInclusion = toUnit _ ≫ n ≫ Q.projection

/-- The two parts of the positive radical and the full scheme stabilizer of the cell. -/
def RootFactors {T B : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (Rpos : ClosedSubgroup B.group) (Rneg : ClosedSubgroup G.val)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (Sminus Splus : Set (Root T)) (A V : ClosedSubgroup G.val)
    (H : ClosedSubgroup B.group) : Prop :=
  let R := subgroupOfSubgroup B Rpos
  IsConjugateIntersection R Rneg A n ∧
  IsConjugateIntersection R R V n ∧
  OrderedParametrization U Sminus A ∧ OrderedParametrization U Splus V ∧
  (∃ (i : A.group ⟶ Rpos.group) (j : V.group ⟶ Rpos.group),
    i ≫ Rpos.inclusion ≫ B.inclusion = A.inclusion ∧
    j ≫ Rpos.inclusion ≫ B.inclusion = V.inclusion ∧
    IsIso (multiplyFactors i j)) ∧
  IsConjugateIntersection B B (subgroupOfSubgroup B H) n ∧
  ∃ (s : T.group ⟶ H.group) (v : V.group ⟶ H.group),
    s ≫ H.inclusion ≫ B.inclusion = T.inclusion ∧
    v ≫ H.inclusion ≫ B.inclusion = V.inclusion ∧
    IsNormalSubgroup v ∧ IsIso (multiplyFactors s v)

/-- Scheme parametrizations of the split Bruhat orbits through the actual Weyl
representatives, with disjointness, the geometric fixed point and the rational
double orbit. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    IsKBorel B → IsSubgroupOf T B →
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (I : Identification D) (U : RootSubgroupFamily T)
        (Bneg : ClosedSubgroup G.val) (Rpos : ClosedSubgroup B.group)
        (Rneg : ClosedSubgroup Bneg.group),
        IsKBorel Bneg ∧ IsSubgroupOf T Bneg ∧
        subgroupRoots T Bneg = (subgroupRoots T B)ᶜ ∧
        IsUnipotentRadical (closedSubgroupAlgebraicGroup B) Rpos ∧
        IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Rneg ∧
        (∀ w, ∃ n, IsRepresentative I w n) ∧
        Nonempty (Presentation B) ∧
        ∀ Q : Presentation B,
          ∃ a : ModObj G.val.X Q.scheme,
            lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
              μ[G.val.X] ≫ Q.projection ∧
            ∀ n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X),
              (∀ w, IsRepresentative I w (n w)) →
              let g := fun w ↦ n w ≫ I.normalizer.inclusion.hom.hom
              let perm := D.rootDatum.weylGroupToPerm
              ∃ (A V : D.rootDatum.weylGroup → ClosedSubgroup G.val)
                (C : ∀ w, Cell (T := T) Q a (g w) (A w)),
                (∀ w, RootFactors U Rpos (subgroupOfSubgroup Bneg Rneg) (g w)
                  (subgroupRoots T B ∩ (perm w '' subgroupRoots T Bneg))
                  (subgroupRoots T B ∩ (perm w '' subgroupRoots T B))
                  (A w) (V w) (C w).stabilizer) ∧
                (∀ w v, w ≠ v →
                  Disjoint (Set.range (C w).orbitInclusion.left)
                    (Set.range (C v).orbitInclusion.left) ∧
                  Disjoint (Set.range (C w).doubleOrbitInclusion.left)
                    (Set.range (C v).doubleOrbitInclusion.left))

end

end LinearAlgebraicGroups.Specs.BruhatOrbitParametrization
