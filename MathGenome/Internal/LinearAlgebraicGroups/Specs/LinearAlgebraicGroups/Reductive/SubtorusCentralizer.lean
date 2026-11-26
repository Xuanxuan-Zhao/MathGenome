import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
import Mathlib.AlgebraicGeometry.Morphisms.Proper

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SubtorusCentralizer

open GeometricBorelConjugacy (IsBorel subgroupOfSubgroup)
open GeometricRadicals
  (IsMaximalTorus IsReductive IsTorus IsUnipotentRadical baseChangedSubgroup)
open QuotientEmbedding (Presentation)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open UnipotentRadicalIntersection (IsSchemeIntersection)

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- The centralizer represents commutation with the subgroup on all test schemes. -/
abbrev IsCentralizer (S C : ClosedSubgroup G) : Prop :=
  RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g)

/-- A subgroup of the centralizer whose image in the ambient group is the scheme
intersection of the centralizer and the given Borel. -/
abbrev IsCentralizerIntersection (C B : ClosedSubgroup G) (D : ClosedSubgroup C.group) :
    Prop :=
  IsSchemeIntersection {C, B} (subgroupOfSubgroup C D)

/-- The orbit through a rational point, as a proper open-and-closed subscheme. -/
structure ProperOrbit {C : GroupScheme k} {Z : SchemeOver k}
    (a : ModObj C.X Z) (z : 𝟙_ (SchemeOver k) ⟶ Z) where
  scheme : SchemeOver k
  inclusion : scheme ⟶ Z
  projection : C.X ⟶ scheme
  factors : projection ≫ inclusion = SmoothOrbit.orbitMap a z
  openImmersion : IsOpenImmersion inclusion.left
  closedImmersion : IsClosedImmersion inclusion.left
  smoothProjection : Smooth projection.left
  surjectiveProjection : Surjective projection.left
  proper : IsProper scheme.hom

/-- On the smooth scheme of S-fixed points of G/B, the centralizer acts with
proper open-and-closed orbits. The orbit of the identity coset is the right
fppf quotient by the scheme intersection of the centralizer and B. -/
def FixedLocusOrbits : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T S : ClosedSubgroup G.val,
      IsMaximalTorus T → IsTorus S.group → IsSubgroupOf S T →
      ∀ C : ClosedSubgroup G.val, IsCentralizer S C →
      ∀ B : ClosedSubgroup G.val, IsBorel B → IsSubgroupOf T B →
      ∀ Q : Presentation B,
        ∃ (a : ModObj G.val.X Q.scheme) (Z : SchemeOver k) (i : Z ⟶ Q.scheme)
          (b : ModObj C.group.X Z),
          (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul = μ[G.val.X] ≫ Q.projection ∧
          IsClosedImmersion i.left ∧
          RepresentsFixedPoints ((S.inclusion.hom.hom ▷ Q.scheme) ≫ a.smul) i ∧
          Smooth Z.hom ∧
          b.smul ≫ i = (C.inclusion.hom.hom ⊗ₘ i) ≫ a.smul ∧
          (∀ z : 𝟙_ (SchemeOver k) ⟶ Z, Nonempty (ProperOrbit b z)) ∧
          ∀ (D : ClosedSubgroup C.group), IsCentralizerIntersection C B D →
            ∀ P : Presentation D,
              ∃ (z : 𝟙_ (SchemeOver k) ⟶ Z) (O : ProperOrbit b z) (e : P.scheme ≅ O.scheme),
                z ≫ i = η[G.val.X] ≫ Q.projection ∧ P.projection ≫ e.hom = O.projection

/-- For every Borel B through T, the centralizer of S in B identifies with
the scheme intersection and is a Borel of the centralizer in G. -/
def CentralizerBorel : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T S : ClosedSubgroup G.val,
      IsMaximalTorus T → IsTorus S.group → IsSubgroupOf S T →
      ∀ C : ClosedSubgroup G.val, IsCentralizer S C →
      ∀ B : ClosedSubgroup G.val, IsBorel B → IsSubgroupOf T B →
        ∃ D : ClosedSubgroup C.group, IsCentralizerIntersection C B D ∧ IsBorel D

/-- In a smooth connected affine group over an algebraically closed field,
the unipotent radical of a subtorus centralizer lies in the ambient radical. -/
def UnipotentRadicalInclusion : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T S : ClosedSubgroup G.val,
      IsMaximalTorus T → IsTorus S.group → IsSubgroupOf S T →
      ∀ C : ClosedSubgroup G.val, IsCentralizer S C →
      ∀ (U : ClosedSubgroup C.group) (R : ClosedSubgroup G.val),
        IsUnipotentRadical (closedSubgroupAlgebraicGroup C) U →
        IsUnipotentRadical G R →
        IsSubgroupOf (subgroupOfSubgroup C U) R

/-- Over any ground field the centralizer of a subtorus of a geometrically
maximal torus in a connected reductive group is reductive. -/
def CentralizerReductive : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T S : ClosedSubgroup G.val,
      IsTorus T.group → IsTorus S.group → IsSubgroupOf S T →
      (∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)) →
      ∃ C : ClosedSubgroup G.val,
        IsCentralizer S C ∧ IsReductive (closedSubgroupAlgebraicGroup C)

end LinearAlgebraicGroups.Specs.SubtorusCentralizer
