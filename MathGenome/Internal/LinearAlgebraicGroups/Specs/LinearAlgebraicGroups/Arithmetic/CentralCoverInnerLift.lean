import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.CentralCoverInnerLift

open CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open AutomorphismSequence

/-- Conjugation by a section of the full adjoint quotient lifts through
a central isogeny of split semisimple groups with marked maximal tori. -/
def InnerAutomorphismLifting : Prop :=
  ∀ {k : Type u} [Field k] (H G : AffineAlgebraicGroup k),
    IsSemisimple H → IsSemisimple G →
    ∀ (T : ClosedSubgroup H.val) (S : ClosedSubgroup G.val),
      IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∀ (q : H.val ⟶ G.val) (qT : T.group ⟶ S.group),
        IsCentralIsogeny q → IsTorusRestriction q qT →
        ∀ (Q : AdjointQuotient G) (inn : groupSections Q.quotient.val ⟶ automorphisms G.val),
          (∀ (V : SchemeOver k) (g : V ⟶ G.val.X),
            inn.app (op V) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g) →
          ∀ (x : (groupSections Q.quotient.val).obj (op (𝟙_ (SchemeOver k))))
            (b : Aut G.val),
            scalarAut b (𝟙_ (SchemeOver k)) = inn.app (op (𝟙_ (SchemeOver k))) x →
            ∃ c : Aut H.val, c.asIso.hom ≫ q = q ≫ b.asIso.hom

end LinearAlgebraicGroups.Specs.CentralCoverInnerLift
