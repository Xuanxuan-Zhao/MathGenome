import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralTorus
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.CentralDerived

open CentralTorus (IsSchemeCentre IsLargestTorus)
open GeometricRadicals (IsReductive IsSemisimple IsTorus GeometricGroup baseChangedSubgroup
  geometricSolvableRadical)
open SchemeDerivedGroup (IsDerivedSubgroup RepresentsQuotient)
open Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

variable {k : Type u} [Field k]

abbrev firstProjection (A B : GroupScheme k) : (A ⊗ B) ⟶ A := fst A B
abbrev secondProjection (A B : GroupScheme k) : (A ⊗ B) ⟶ B := snd A B

/-- The homomorphism from the direct product is given by multiplication of the two inclusions. -/
def IsCentralProduct {G : GroupScheme k} {Z : ClosedSubgroup G}
    (T : ClosedSubgroup Z.group) (D : ClosedSubgroup G) (m : (T.group ⊗ D.group) ⟶ G) : Prop :=
  m.hom.hom = (firstProjection T.group D.group ≫ T.inclusion ≫ Z.inclusion).hom.hom *
    (secondProjection T.group D.group ≫ D.inclusion).hom.hom

/-- The kernel identifies with the scheme intersection via the diagonal with inversion
in the second coordinate. Both pullbacks are scheme-theoretic. -/
def HasCentralProductKernel {G : GroupScheme k} {Z : ClosedSubgroup G}
    {T : ClosedSubgroup Z.group} {D : ClosedSubgroup G} (m : (T.group ⊗ D.group) ⟶ G) : Prop :=
  ∃ (I : GroupScheme k) (p : I ⟶ T.group) (q : I ⟶ D.group)
    (J : ClosedSubgroup (T.group ⊗ D.group)),
    IsPullback p q (T.inclusion ≫ Z.inclusion) D.inclusion ∧
    IsFinite I.X.hom ∧
    ∃ e : I ≅ J.group,
      (e.hom ≫ J.inclusion ≫ firstProjection T.group D.group) = p ∧
      (e.hom ≫ J.inclusion ≫ secondProjection T.group D.group).hom.hom = q.hom.hom⁻¹ ∧
      IsSchemeKernel m J ∧ ∀ (Y : SchemeOver k) (g : Y ⟶ (T.group ⊗ D.group).X),
        Centralizes J.inclusion g

def CentralTorusExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∃ Z : ClosedSubgroup G.val, IsSchemeCentre Z ∧
      ∃ T : ClosedSubgroup Z.group, IsLargestTorus T ∧
        ∀ (K : Type u) [Field K] [Algebra k K],
          ∃ (hZ : IsClosedImmersion ((groupBaseChange k K).map Z.inclusion).hom.hom.left)
            (hT : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left),
            IsSchemeCentre (baseChangedSubgroup K Z hZ) ∧
              IsLargestTorus (baseChangedSubgroup K T hT)

def CentralProductKernel : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Z : ClosedSubgroup G.val), IsSchemeCentre Z →
    ∀ (T : ClosedSubgroup Z.group), IsLargestTorus T →
    ∀ (D : ClosedSubgroup G.val), IsDerivedSubgroup D →
      ∃ m : (T.group ⊗ D.group) ⟶ G.val, IsCentralProduct T D m ∧ HasCentralProductKernel m

def CentralProductFaithfullyFlat : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Z : ClosedSubgroup G.val), IsSchemeCentre Z →
    ∀ (T : ClosedSubgroup Z.group), IsLargestTorus T →
    ∀ (D : ClosedSubgroup G.val), IsDerivedSubgroup D →
    ∀ m : (T.group ⊗ D.group) ⟶ G.val, IsCentralProduct T D m →
      Flat m.hom.hom.left ∧ Surjective m.hom.hom.left

def DerivedTorusQuotient : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (D : ClosedSubgroup G.val), IsDerivedSubgroup D →
      ∃ (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
        IsSchemeKernel q D ∧ RepresentsQuotient D q ∧ IsTorus Q.val

def DerivedSemisimple : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (D : ClosedSubgroup G.val), IsDerivedSubgroup D →
      IsSemisimple (closedSubgroupAlgebraicGroup D)

def GeometricSolvableRadical : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Z : ClosedSubgroup G.val), IsSchemeCentre Z →
    ∀ (T : ClosedSubgroup Z.group), IsLargestTorus T →
      ∃ e : (geometricSolvableRadical G).group ≅ (groupBaseChange k (AlgebraicClosure k)).obj T.group,
        e.hom ≫ (groupBaseChange k (AlgebraicClosure k)).map (T.inclusion ≫ Z.inclusion) =
          (geometricSolvableRadical G).inclusion

def SemisimpleIffFiniteCentre : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Z : ClosedSubgroup G.val), IsSchemeCentre Z →
      (IsSemisimple G ↔ IsFinite Z.group.X.hom)

end

end LinearAlgebraicGroups.Specs.CentralDerived
