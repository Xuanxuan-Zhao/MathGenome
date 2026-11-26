import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.GroupTheory.Torsion

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.CentralTorus

open GeometricRadicals (IsReductive IsTorus baseChangedSubgroup)
open DiagonalizableGroups (FGAbelianGroup groupAlgebra diagonalClosedInclusion)
open SchemeDerivedGroup (IsDerivedSubgroup IsSubgroupOf)

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- The scheme centre is the centralizer of the entire group. -/
def IsSchemeCentre (Z : ClosedSubgroup G) : Prop :=
  RepresentsSubgroup Z (fun _ g ↦ Centralizes (𝟙 G) g)

/-- The largest torus in the centre, with its closed immersion into the centre. -/
def IsLargestTorus {Z : GroupScheme k} (T : ClosedSubgroup Z) : Prop :=
  IsTorus T.group ∧ ∀ S : ClosedSubgroup Z, IsTorus S.group → IsSubgroupOf S T

/-- The scheme centre of a connected reductive group is of multiplicative type. -/
def CentreMultiplicativeType : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∃ Z : ClosedSubgroup G.val, IsSchemeCentre Z ∧
      ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E)
        (M : FGAbelianGroup.{u}),
        Nonempty ((groupBaseChange k E).obj Z.group ≅ specGroup (groupAlgebra E M.obj))

/-- The largest torus exists and its closed immersion into the centre is preserved
under every field extension. The extended centre is the scheme centre. -/
def LargestCentralTorus : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ Z : ClosedSubgroup G.val, IsSchemeCentre Z →
      ∃ T : ClosedSubgroup Z.group, IsLargestTorus T ∧
        ∀ (K : Type u) [Field K] [Algebra k K],
          ∃ (hZ : IsClosedImmersion ((groupBaseChange k K).map Z.inclusion).hom.hom.left)
            (hT : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left),
            IsSchemeCentre (baseChangedSubgroup K Z hZ) ∧
              IsLargestTorus (baseChangedSubgroup K T hT)

/-- In a diagonalizable presentation of the centre the torus is defined by quotienting
the full character group by torsion. This applies over any field splitting the centre. -/
def SplitCentralTorus : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Z : ClosedSubgroup G.val), IsSchemeCentre Z →
      ∀ (T : ClosedSubgroup Z.group), IsLargestTorus T →
        ∀ (M : FGAbelianGroup.{u}) (e : Z.group ≅ specGroup (groupAlgebra k M.obj)),
          ∃ j : T.group ≅ specGroup (groupAlgebra k (M.obj ⧸ CommGroup.torsion M.obj)),
            j.hom ≫ diagonalClosedInclusion k (CommGroup.torsion M.obj) = T.inclusion ≫ e.hom

/-- The intersection with the scheme-theoretic derived group is finite over the field.
The group-scheme pullback retains all scheme structure. -/
def CentralTorusDerivedIntersectionFinite : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Z : ClosedSubgroup G.val), IsSchemeCentre Z →
      ∀ (T : ClosedSubgroup Z.group), IsLargestTorus T →
        ∀ (D : ClosedSubgroup G.val), IsDerivedSubgroup D →
          ∃ (I : GroupScheme k) (p : I ⟶ T.group) (q : I ⟶ D.group),
            IsPullback p q (T.inclusion ≫ Z.inclusion) D.inclusion ∧ IsFinite I.X.hom

end LinearAlgebraicGroups.Specs.CentralTorus
