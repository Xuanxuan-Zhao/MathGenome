import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.TorusFreeUnipotent

open GeometricBorelConjugacy (IsBorel)
open GeometricRadicals (GeometricGroup IsMaximalTorus IsTorus IsTrivialSubgroup)
open SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open Unipotent (IsFppfGroupQuotient IsUnipotent closedSubgroupAlgebraicGroup)

/-- A smooth connected affine algebraic group with only trivial geometric tori is unipotent. -/
def Unipotence : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    (∀ T : ClosedSubgroup (GeometricGroup G).val, IsTorus T.group → IsTrivialSubgroup T) →
    IsUnipotent G

/-- Over an algebraically closed field, the centralizer of a maximal torus
has unipotent quotient by that torus and is solvable. It lies in every Borel
containing the torus. The quotient is the right fppf quotient. -/
def MaximalTorusCentralizer : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T : ClosedSubgroup G.val, IsMaximalTorus T →
    ∃ C : ClosedSubgroup G.val,
      RepresentsSubgroup C (fun _ g ↦ Centralizes T.inclusion g) ∧
      Smooth C.group.X.hom ∧ GeometricallyConnected C.group.X.hom ∧
      IsSolvable C.group ∧
      (∀ B : ClosedSubgroup G.val, IsBorel B → IsSubgroupOf T B → IsSubgroupOf C B) ∧
      ∃ (j : T.group ⟶ C.group) (hj : IsClosedImmersion j.hom.hom.left)
        (Q : AffineAlgebraicGroup k) (q : C.group ⟶ Q.val),
        j ≫ C.inclusion = T.inclusion ∧
        IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup C) ⟨_, j, hj⟩ q ∧
        IsUnipotent Q

end LinearAlgebraicGroups.Specs.TorusFreeUnipotent
