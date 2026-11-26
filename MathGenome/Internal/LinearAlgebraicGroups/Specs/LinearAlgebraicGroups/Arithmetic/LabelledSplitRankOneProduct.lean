import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.EuclideanComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LabelledSplitRankOneProduct

open GeometricRadicals (IsSemisimple)
open Pinning (AttachedDatum SplitBorelPair)
open RootGroups (IsRootSubgroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open StandardGroups (specialLinearPoints)

/-- The product of split rank-one groups with its specified simple root subgroups. -/
def Statement : Prop :=
  ∀ (F I : Type u) [Field F] [Finite I] [Nonempty I]
    (P : SplitBorelPair F) (D : AttachedDatum P),
    IsSemisimple P.G → GeometricallySimplyConnected P.G →
    letI := D.comm
    ∀ (label : I ≃ D.base.support),
      (∀ i j, i ≠ j → RootData.integralCartan D.datum.rootDatum D.base (label i) (label j) = 0) →
      ∀ (V : I → ClosedSubgroup P.G.val),
        (∀ i, IsRootSubgroup P.T (V i) (label i).val.val) →
        ∃ (S : AffineAlgebraicGroup F)
          (s : (groupPointsFunctor F).obj S.val ≅ specialLinearPoints F (ULift.{u} (Fin 2)))
          (π : ∀ _ : I, P.G.val ⟶ S.val),
          Nonempty (IsLimit (Fan.mk P.G.val π)) ∧
          ∀ i,
            (∀ j, j ≠ i → (V i).inclusion ≫ π j = 0) ∧
            IsClosedImmersion ((V i).inclusion ≫ π i).hom.hom.left ∧
            ∀ R : TestAlgebra F,
              Set.range (fun p : Points (V i).group.X R =>
                (s.hom.app R (p ≫ ((V i).inclusion ≫ π i).hom.hom)).val) =
              Set.range (fun a : R => (1 + Matrix.single ⟨0⟩ ⟨1⟩ a :
                Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) R))

end LinearAlgebraicGroups.Specs.Arithmetic.LabelledSplitRankOneProduct
