import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Mathlib.Basic.Complex.Basic

namespace LinearAlgebraicGroups.Specs.ComplexExceptionalDatum

open AbsoluteDynkinTypes (HasDynkinType IsAbsolutelyAlmostSimple)
open GeometricRadicals (GeometricGroup IsReductive)
open Pinning (AttachedDatum SplitBorelPair)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)

/-- The based Cartan matrix has exceptional type E₆, E₇ or E₈. -/
def HasExceptionalCartan {k : Type} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) : Prop :=
  letI := D.comm
  let A := RootData.integralCartan D.datum.rootDatum D.base
  HasDynkinType A .E6 ∨ HasDynkinType A .E7 ∨ HasDynkinType A .E8

/-- The absolute exceptional type is witnessed on the actual geometric group. -/
def HasExceptionalType (G : AffineAlgebraicGroup ℝ) : Prop :=
  ∃ (P : SplitBorelPair (AlgebraicClosure ℝ)) (_ : P.G = GeometricGroup G)
    (D : AttachedDatum P), HasExceptionalCartan D

/-- On the actual complexification, every attached based datum has full
coroot lattice and the given exceptional type. -/
def Statement : Prop :=
  ∀ G : AffineAlgebraicGroup ℝ, IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G → HasExceptionalType G →
    let H := Unipotent.baseChangedAlgebraicGroup ℂ G
    IsReductive H ∧
      ∀ (P : SplitBorelPair ℂ), P.G = H →
        ∀ D : AttachedDatum P, corootLattice D = ⊤ ∧ HasExceptionalCartan D

end LinearAlgebraicGroups.Specs.ComplexExceptionalDatum
