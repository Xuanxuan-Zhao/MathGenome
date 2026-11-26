import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry LieAlgebrasAndRepresentations

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalCompletionGeometry

open AbsoluteDynkinTypes (HasDynkinType IsAbsolutelyAlmostSimple)
open GeometricRadicals (GeometricGroup)
open Pinning (AttachedDatum SplitBorelPair)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

/-- Dynkin type on an attached datum of the geometric group. -/
def HasAbsoluteType {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (t : FiniteDynkinType) : Prop :=
  ∃ (P : SplitBorelPair (AlgebraicClosure F)) (_ : P.G = GeometricGroup G)
    (D : AttachedDatum P),
    letI := D.comm
    HasDynkinType (RootData.integralCartan D.datum.rootDatum D.base) t

/-- Geometric properties of the exceptional group after scalar extension
along the canonical algebra of the real completion. -/
def RealCompletionGeometricExtension : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] (G : AffineAlgebraicGroup K)
    (w : NumberField.InfinitePlace K), w.IsReal →
    ∀ t : FiniteDynkinType, (t = .E6 ∨ t = .E7 ∨ t = .E8) →
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasAbsoluteType G t →
      let Gv := baseChangedAlgebraicGroup w.Completion G
      IsAbsolutelyAlmostSimple Gv ∧ GeometricallySimplyConnected Gv ∧ HasAbsoluteType Gv t

end LinearAlgebraicGroups.Specs.ExceptionalCompletionGeometry
